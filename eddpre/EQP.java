/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */

package coins.ssa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.DFST;
import coins.backend.ana.Dominators;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirNode;
import coins.backend.sym.Symbol;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

/**
 * Effective Demand Driven PRE
 * 
 **/

public class EQP implements LocalTransformer {
	public boolean doIt(Data data, ImList args) {return true;}
	public String name() {return "EQP";}
	public String subject() {return "Optimizatin with efficient question propagation.";}
	private String tmpSymName = "_eqp";
	private Util util;
	public static final int THR = SsaEnvironment.OptThr;
	/** The threshold of debug print **/
	public static final int THR2 = SsaEnvironment.AllThr;
	private SsaEnvironment env;
	private SsaSymTab sstab;
	private Function f;
	BasicBlk[] bVecInOrderOfRPost;
	public GVN gvn;
	EMemoryAliasAnalyze alias;
	private DFST dfst;
	public Dominators dom;
	int idBound;
	
	Target target;
	Print print;
	
	/**
	 * Constructor
	 * 
	 * @param e The environment of the SSA module
	 * @param tab The symbol tabel of the SSA module
	 * @param function The current function
	 * @param m The current mode
	 **/
	public EQP(SsaEnvironment e, SsaSymTab tab, int m) {
		env = e;
		env.println(" Effective Demand-driven Patial Redundancy Elimination on SSA form", SsaEnvironment.MsgThr);
		sstab = tab;
		// 1:all speculate code motion.
		// 2:speculate code motion for loop-invariant code only.
		// 3:do not speculate code motion.
		mode = 2;
	}
	
	public EQP(SsaEnvironment e, Function func, SsaSymTab sstab){
    	this.f = func;
    	this.env=e;
    	this.sstab = sstab;
    	mode = 2;
	}
	
	HashSet dependPhiSet;
	BasicBlk exprBlk;
	HashMap visited;
	HashSet[] result;
	int[] avail;
	HashSet[] isReal;
	HashSet[] isSelf;
	HashMap blkToNewNode;
	public ArrayList newNodes;
	public HashMap insertNodeToBlk;
	public int[] blkVal;
	public boolean[] kill;
	int mode;
	
	/**
	 * Do optimize using Effective Question Propagation.
	 * 
	 * @param f
	 **/
	public boolean doIt(Function function, ImList args) {
		f = function;
		invoke(1);
		f.flowGraph().touch();
		return (true);
	}
	
	
	/**
	 *  mode: 1 --> all redundant expressions are eliminated.
	 *        2 --> MEM expressions are not eliminated.
	 *        3 --> none of expressions which are eliminated.
	 * @param mode
	 */
	public void invoke(int mode){
		print = new Print(env,f);
		set();
		gvn(mode);
		eliminate(mode);
		alias.annul();
	}
	
	
	public void set(){
		alias=new EMemoryAliasAnalyze(env,f);
		dom = (Dominators) f.require(Dominators.analyzer);
		dfst = (DFST) f.require(DFST.analyzer);
		bVecInOrderOfRPost = dfst.blkVectorByRPost();
		util = new Util(env, f);
		gvn = new GVN(env,f,sstab);
		idBound = f.flowGraph().idBound();
		dependPhiSet = new HashSet();
		kill = new boolean[idBound];
		collectInformation();
	}
	
	
	public void gvn(int mode){
		gvn.gvn(mode);
	}
	
	
	private void collectInformation(){
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode==Op.CALL || node.opCode==Op.SET && node.kid(0).opCode==Op.MEM) kill[blk.id] = true;
				if(node.opCode==Op.PHI) dependPhiSet.add(node.kid(0));
				if(node.opCode==Op.SET && node.kid(0).opCode==Op.REG){
					if(node.kid(1).nKids()==0){
						if(dependPhiSet.contains(node.kid(1))) dependPhiSet.add(node.kid(0));
					}else{
						for(int j=0;j<node.kid(1).nKids();j++){
							if(dependPhiSet.contains(node.kid(1).kid(j))){
								dependPhiSet.add(node.kid(0));
								break;
							}
						}
					}
				}
			}
		}
	}
	
	
	public void setVarsToGCM(BasicBlk blk, int val){
		result = new HashSet[idBound];
//		avail = new HashSet[idBound];
		avail = new int[idBound];
		isReal = new HashSet[idBound];
		isSelf = new HashSet[idBound];
		visited = new HashMap(idBound);
		exprBlk = blk;
		insertNodeToBlk = new HashMap();
		newNodes = new ArrayList();
		blkToNewNode = new HashMap();
		blkVal = new int[idBound];
	}
	
	
	private void eliminate(int mode){
		HashSet insertNodes = new HashSet();
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			boolean kill = false;
			HashMap valueMap = new HashMap();
			HashSet blkValueMap = new HashSet();
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode==Op.CALL || node.opCode==Op.SET && node.kid(0).opCode==Op.MEM) kill = true;
				if(node.opCode==Op.PHI){
					int val = gvn.getValue(node.kid(0));
					blkValueMap.add(val);
					valueMap.put(val, node.kid(0));
				}else if(node.opCode==Op.CALL && node.kid(2).nKids()>0){
					int val = gvn.getValue(node.kid(2).kid(0));
					blkValueMap.add(val);
					valueMap.put(val, node.kid(2).kid(0));
				}else if(node.opCode==Op.PROLOGUE){
					for(int j=0;j<node.nKids();j++){
						if(node.kid(j).opCode!=Op.REG)continue;
						int val = gvn.getValue(node.kid(j));
						blkValueMap.add(val);
						valueMap.put(val, node.kid(j));
					}
				}
				if(node.opCode!=Op.SET || insertNodes.contains(node))continue;
				
				LirNode ve = gvn.makeVExp(node,blk);
				int val = gvn.getValue(ve);
				
				if(val==-1){
					if(node.kid(0).opCode==Op.MEM){
						LirNode mv = gvn.makeVExp(node.kid(0),blk);
						int old = gvn.getValue(mv);
						gvn.removeValue(mv,ve,old,blk);
						val = gvn.newValue();
						gvn.setValue(val,mv,blk);
					}else{
						int old = gvn.getValue(node.kid(0));
						gvn.removeValue(node.kid(0),ve,old,blk);
						val = gvn.newValue();
						gvn.setValue(val,ve,blk);
						gvn.setValue(val,node.kid(0),blk);
					}
				}
				
				if(valueMap.containsKey(val)){
					if(node.kid(1).nKids()>0 && (mode==1 || mode==2 && node.kid(1).opCode!=Op.MEM)){
						LirNode pred = (LirNode)valueMap.get(val);
						node.setKid(1, pred.makeCopy(env.lir));
					}
					if(node.kid(0).opCode==Op.REG && node.kid(1).nKids()!=0) valueMap.put(val, node.kid(0));
					else valueMap.put(val, node.kid(1));
					blkValueMap.add(val);
					continue;
				}
				
				if(node.kid(1).nKids()==0 || (kill || mode==2 || mode==3) && node.kid(1).opCode==Op.MEM){
					if(node.kid(0).opCode==Op.REG) valueMap.put(val, node.kid(0));
					else valueMap.put(val, node.kid(1));
					gvn.setValue(val, node.kid(0), ve, blk);
					blkValueMap.add(val);
					continue;
				}
				
				setVarsToGCM(blk,val);
				LirNode copy = node.makeCopy(env.lir);
				LirNode vnode = node.makeCopy(env.lir);
				vnode.setKid(1, ve);
				
				if(propagate(val,vnode,copy,blk) && changeNameNewNodes(node,p)){
					val = changeProg(node,ve,blk,val,p);
				}
				
				gvn.setValue(val,node.kid(0),ve,blk);
				valueMap.put(val, node.kid(0));
				blkValueMap.add(val);
				
				if(node.kid(1).opCode==Op.REG) insertNodes.addAll(newNodes);
				else cancelInsertNode();
			}
			gvn.updateBlkVariableMap(blk, valueMap);
			gvn.updateReachableValues(blk,blkValueMap);
		}
	}
	
	
	public boolean propagate(int val, LirNode vnode, LirNode node, BasicBlk blk){
		int True = 0;
		int Real = 0;
		int Self = 0;
		ArrayList blks = new ArrayList(blk.predList().length());
		HashMap newNodes = new HashMap();
		for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
			BasicBlk pred = (BasicBlk)p.elem();
			LirNode newNode = node.makeCopy(env.lir);
			LirNode newVNode = vnode.makeCopy(env.lir);
			
			// change node for propagating the predecessor node.
			// first, change the index of memory which was assigned by EMemoryAlias.
			if(node.kid(1).opCode==Op.MEM){
				LirNode inode = alias.getIndex(pred);
				LirNode newIndex = gvn.makeVExp(inode,pred).makeCopy(env.lir);
				newVNode.kid(1).setKid(1, newIndex);
				node.kid(1).setKid(1, inode);
			}
			
			// make node whose each leaf is changed to its value number.
			LirNode newVExp = gvn.makeNewValueExp(newVNode.kid(1),node.kid(1),blk,pred);
			newVNode.setKid(1, newVExp);
			
			// make complete node.
			LirNode newExp = gvn.valueNumberToVariable(newVExp,node.kid(1),pred,null);
			if(newExp==null){
				recordResult(val,blk);
				return false;
			}
			if(node.kid(1).opCode==Op.MEM) newExp.setKid(1, node.kid(1).kid(1));
			
			newNode.setKid(1, newExp);
			int newVal = gvn.getValue(newVExp);
			
			if(newVal==-1){
				boolean setNewVal = true;
				if(node.kid(1).opCode==Op.MEM){
					LirNode tempExp = newVExp.makeCopy(env.lir);
					tempExp.setKid(1, vnode.kid(1).kid(1));
					int temp = gvn.getValue(tempExp);
					if(temp!=-1){
						newVNode.kid(1).setKid(1, vnode.kid(1).kid(1));
						newNode.kid(1).setKid(1, node.kid(1).kid(1));
						newVal = temp;
						setNewVal = false;
					}
				}
				if(setNewVal){
					gvn.setValue(gvn.newValue(), newVExp, pred);
					newVal = gvn.getValue(newVExp);
				}
			}
			
			boolean localAnswer;
			if(checkVisited(pred)){
				if(checkResult(newVal,pred)) localAnswer = checkAvail(newVal,pred);
				else localAnswer = visitedSameVal(newVal,pred);
			}else{
				newNodes.put(pred, newNode);
				blkVal[pred.id] = newVal;
				localAnswer = local(newVal,newVNode,newNode,pred);
			}
			
			if(localAnswer){
				True++;
				if(checkIsReal(newVal,pred)) Real++;
				if(checkIsSelf(newVal,pred)) Self++;
			}else{
				blks.add(pred);
			}
		}
		recordResult(val,blk);
		recordVisited(val,blk);
		boolean checkDSafe = mode==2 && Self!=blk.predList().length() || mode==3;
		if(True>0){
			if(blks.size()>0){
				if(Real==0 || checkDSafe && !checkDSafe(val,vnode.kid(1),node.kid(1),blk))return false;
				insertTempNewNode(newNodes,blks);
				insertNewTempPhi(val,node,blk);
				Real = blk.predList().length();
			}else if(blk.predList().length()>1){
				if(True!=Real && checkDSafe && !checkDSafe(val,vnode.kid(1),node.kid(1),blk))return false;
				insertNewTempPhi(val,node,blk);
				Real = blk.predList().length();
			}
			recordAvail(val,blk);
			if(Real>0)recordIsReal(val,blk);
			if(Self==blk.predList().length())recordIsSelf(val,blk);
			return true;
		}
		return false;
	}
	
	
	private boolean local(int val, LirNode vnode, LirNode node, BasicBlk blk){
		recordVisited(val,blk);
		boolean answer = false;
		if(gvn.containValue(val,blk) && (node.kid(1).opCode!=Op.MEM || !kill[blk.id] || checkMemKill(val,node,blk))){
			recordAvail(val,blk);
			recordIsReal(val,blk);
			if(blk==exprBlk)recordIsSelf(val,blk);
			answer = true;
		}else if(node.kid(1).opCode==Op.MEM && kill[blk.id]){
			answer = false;
		}else if((gvn.reachValue(val, blk) || dependPhi(node.kid(1),blk)) && blk!=exprBlk){
			answer = propagate(val,vnode,node,blk);
		}
		recordResult(val,blk);
		return answer;
	}
	
	
	/**
	 * Check local property of basic block which generate origin query.
	 * @param val
	 * @param node
	 * @param blk
	 * @return
	 */
	boolean checkMemKill(int val, LirNode node, BasicBlk blk){
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode n = (LirNode)p.elem();
			if(n.opCode==Op.SET){
				if(n.kid(0).opCode==Op.MEM){
					if(gvn.getValue(n.kid(1))==val) return true;
					else break;
				}else if(gvn.getValue(n.kid(0))==val)return true;
			}
			if(n.opCode==Op.CALL) break;
		}
		return false;
	}
	
	
	public void insertTempNewNode(LirNode node, int val, BasicBlk blk){
		if(!insertNodeToBlk.containsValue(blk)){
			node.setKid(0, createNewVar(node.kid(0),tmpSymName));
			if(node.kid(1).opCode==Op.MEM) node.setKid(1, alias.makeNewMem(node.kid(1)));
			node = node.makeCopy(env.lir);
			addToNewNodes(node);
			insertNodeToBlk.put(node, blk);
			gvn.setValue(val, node.kid(0), blk);
		}
	}
	
	
	public void insertTempNewNode(HashMap newNodes, ArrayList blks){
		for(int i=0;i<blks.size();i++){
			BasicBlk blk = (BasicBlk)blks.get(i);
			int val = blkVal[blk.id];
			if(val==-1)val = gvn.newValue();
			LirNode node = (LirNode)newNodes.get(blk);
			insertTempNewNode(node, val, blk);
		}
	}
	
	
	public void insertNewTempPhi(int val, LirNode node, BasicBlk blk){
		if(!existDomBlk(val,node.kid(1),blk)){
			LirNode newPhi = null;
			boolean remove = false;
			if(newNodes.size()>0 && insertNodeToBlk.containsValue(blk)){
				for(int i=0;i<newNodes.size();i++){
					newPhi = (LirNode)newNodes.get(i);
					if(newPhi.opCode!=Op.PHI || (((LirLabelRef) newPhi.kid(1).kid(2)).label).basicBlk()!=blk)continue;
					newNodes.remove(i);
					insertNodeToBlk.remove(newPhi);
					gvn.removeValue(val, newPhi.kid(0), blk);
					remove = true;
					break;
				}
			}
			
			if(!remove){
				newPhi = (newPhi(node,blk,tmpSymName)).makeCopy(env.lir);
			}
			
			addToNewNodes(newPhi);
			newPhi = newPhi.makeCopy(env.lir);
			insertNodeToBlk.put(newPhi, blk);
			gvn.setValue(val, newPhi.kid(0), blk);
		}
	}
	
	
	public boolean existDomBlk(int val, LirNode exp, BasicBlk blk){
		for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
			BasicBlk pred = (BasicBlk)p.elem();
			BasicBlk domBlk = pred;
			while(domBlk!=null){
				if(!checkVisited(domBlk) || val!=blkVal[domBlk.id]) return false;
				if(gvn.containValue(val, domBlk) && dom.dominates(domBlk, blk)) break;
				if(insertNodeToBlk.containsValue(domBlk))return false;
				domBlk = dom.immDominator(domBlk);
			}
			if(domBlk==null) return false;
		}
		return true;
	}
	
	public boolean checkResult(int val, BasicBlk blk){
		if(result[blk.id]==null)return false;
		HashSet list = result[blk.id];
		return list.contains(val);
	}
	
	
	public void recordResult(int val, BasicBlk blk){
		if(result[blk.id]==null){
			HashSet list = new HashSet();
			result[blk.id] = list;
		}
		HashSet list = result[blk.id];
		list.add(val);
	}
	
	
	public boolean checkAvail(int val, BasicBlk blk){
		return (avail[blk.id]==val);
	}
	
	
	public void recordAvail(int val, BasicBlk blk){
		avail[blk.id] = val;
	}
		
//	public boolean checkAvail(int val, BasicBlk blk){
//		if(avail[blk.id]==null)return false;
//		HashSet list = avail[blk.id];
//		return list.contains(val);
//	}
//	
//	
//	public void recordAvail(int val, BasicBlk blk){
//		if(avail[blk.id]==null){
//			HashSet list = new HashSet();
//			avail[blk.id] = list;
//		}
//		HashSet list = avail[blk.id];
//		list.add(val);
//	}
	
	
	public boolean checkIsReal(int val, BasicBlk blk){
		if(isReal[blk.id]==null)return false;
		HashSet list = isReal[blk.id];
		return list.contains(val);
	}
	
	
	public void recordIsReal(int val, BasicBlk blk){
		if(isReal[blk.id]==null){
			HashSet list = new HashSet();
			isReal[blk.id] = list;
		}
		HashSet list = isReal[blk.id];
		list.add(val);
	}
	
	
	public boolean checkIsSelf(int val, BasicBlk blk){
		if(isSelf[blk.id]==null)return false;
		HashSet list = isSelf[blk.id];
		return list.contains(val);
	}
	
	
	public void recordIsSelf(int val, BasicBlk blk){
		if(isSelf[blk.id]==null){
			HashSet list = new HashSet();
			isSelf[blk.id] = list;
		}
		HashSet list = isSelf[blk.id];
		list.add(val);
	}
	
	
	public boolean checkVisited(BasicBlk blk){
		return visited.containsKey(blk);
	}
	
	
	public boolean visitedSameVal(int val, BasicBlk blk){
		return (val==(Integer)visited.get(blk));
	}
	
	
	public void recordVisited(int val, BasicBlk blk){
		visited.put(blk, val);
	}
	
	
	public LirNode createNewVar(LirNode typeNode, String tmpSymName){
		Symbol dstSym = sstab.newSsaSymbol(tmpSymName, typeNode.type);
		return env.lir.symRef(Op.REG, typeNode.type, dstSym, ImList.Empty);
	}
	
	
	public LirNode newPhi(LirNode expr, BasicBlk blk, String tmpSymName){
		Symbol sym = sstab.newSsaSymbol(tmpSymName, expr.type);
		return util.makePhiInst(sym, blk);
	}
	
	
	public boolean checkDSafe(int val, LirNode ve, LirNode expr, BasicBlk blk){
		if(gvn.containValue(val,blk)) return true;
		boolean[] checkBlk = new boolean[idBound];
		for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
			BasicBlk succ = (BasicBlk)p.elem();
			if(checkBlk[succ.id])continue;
			LirNode newVExp = gvn.makeNewValueExp(ve,expr,succ);
			int newVal = gvn.getValue(newVExp);
			if(newVal==-1 || !checkDSafe(newVal,newVExp,expr,succ,checkBlk)) return false;
		}
		return true;
	}
	
	
	public boolean checkDSafe(int val, LirNode ve, LirNode expr, BasicBlk blk, boolean[] checkBlk){
		checkBlk[blk.id] = true;
		if(gvn.containValue(val,blk)) return true;
		else if(blk==f.flowGraph().exitBlk()) return false;
		else{
			for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
				BasicBlk succ = (BasicBlk)p.elem();
				if(checkBlk[succ.id])continue;
				LirNode newVExp = gvn.makeNewValueExp(ve,expr,succ);
				int newVal = gvn.getValue(newVExp);
				if(newVal==-1 || !checkDSafe(newVal,newVExp,expr,succ,checkBlk)) return false;
			}
			return true;
		}
	}
	
	
	boolean dependPhi(LirNode exp, BasicBlk blk){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG){
				if(dependPhiSet.contains(exp.kid(i)))return true;
			}else if(exp.kid(i).nKids()>0){
				if(dependPhi(exp.kid(i),blk)) return true;
			}
		}
		return false;
	}
	
	public LirNode getVarLocal(int val, BiLink q){
		LirNode var = null;
		for(BiLink p=q;!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
			if(node.opCode!=Op.SET && node.opCode!=Op.PHI)continue;
			if(insertNodeToBlk.containsKey(node)){
				if(node.kid(1).nKids()==0) var = node.kid(1);
				else var = node.kid(0);
				break;
			}else if(node.kid(0).opCode==Op.REG){
				if(gvn.getValue(node.kid(0))==val){
					if(node.kid(1).nKids()==0) var = node.kid(1);
					else var = node.kid(0);
					break;
				}
			}else if(gvn.getValue(node.kid(1))==val){
				var = node.kid(1);
				break;
			}
		}
		return var;
	}
	
	
	/**
	 * return before node which has same value.
	 * @param val
	 * @param blk
	 * @param q
	 * @return
	 */
	private LirNode getVar(int val, BasicBlk blk, BiLink q){
		BasicBlk domBlk = blk;
		if(q!=null){
			// local
			if(containNewNode(blk) || gvn.containValue(val,blk)){
				LirNode var = getVarLocal(val,q);
				if(var!=null) return var;
			}
			domBlk = dom.immDominator(blk);
		}
		
		while(domBlk!=null){
			val = blkVal[domBlk.id];
			if(gvn.containValue(val,domBlk)) return gvn.getVariable(val,domBlk);
			else if(containNewNode(domBlk)) return getNewNode(domBlk).kid(0);
			if(!checkAvail(val,domBlk)) break;
			domBlk = dom.immDominator(domBlk);
		}
		return null;
	}
	
	
	public boolean containNewNode(BasicBlk blk){
		return (blkToNewNode.containsKey(blk));
	}
	
	
	public LirNode getNewNode(BasicBlk blk){
		return (LirNode)blkToNewNode.get(blk);
	}
	
	
	public void removeFromNewNodes(LirNode node){
		newNodes.remove(node);
	}
	
	
	public void addToNewNodes(LirNode node){
		newNodes.add(node);
	}
	
	
	public BasicBlk getBlkFromInsertNodeToBlk(LirNode node){
		if(!insertNodeToBlk.containsKey(node))return null;
		else return (BasicBlk)insertNodeToBlk.get(node);
	}
	
	
	public void putEntryToInsertNodeToBlk(LirNode node, BasicBlk blk){
		insertNodeToBlk.put(node, blk);
	}
	
	
	public void putEntryToBlkToNewNode(LirNode node, BasicBlk blk){
		blkToNewNode.put(blk, node);
	}
	
	
	public int changeProg(LirNode node, LirNode ve, BasicBlk blk, int val, BiLink p){
		LirNode predNode = getVar(val,blk,p.prev());
		return changeProg(node,ve,predNode,blk,val,p);
	}
	
	
	public int changeProg(LirNode node, LirNode ve, LirNode predNode, BasicBlk blk, int val, BiLink p){
		replace(node,predNode);
		int newVal = gvn.getValue(predNode);
		if(newVal==-1)newVal = gvn.newValue();
		if(val!=newVal)gvn.removeValue(node.kid(0),ve,val,blk);
		return newVal;
	}
	
	
	public void replace(LirNode node, LirNode pred){
		LirNode dst = null;
		if(pred.opCode==Op.SET){
			if(pred.kid(0).opCode==Op.REG) dst = pred.kid(0);
			else dst = pred.kid(1);
		}else if(pred.opCode==Op.PHI) dst = pred.kid(0);
		else dst = pred;
		node.setKid(1, dst.makeCopy(env.lir));
	}
	
	
	public void insert(LirNode node, BasicBlk blk){
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode n = (LirNode)p.elem();
			if(n.opCode!=Op.PHI){
				p.addBefore(node);
				break;
			}
		}
	}
	
	
	/**
	 * change variables of new nodes.
	 * @param expr
	 * @param valueMap
	 * @return
	 */
	public boolean changeNameNewNodes(LirNode expr, BiLink q){
		HashSet newSetNode = new HashSet();
		for(int i=0;i<newNodes.size();i++){
			LirNode node = (LirNode)newNodes.get(i);
			if(newSetNode.contains(node))continue;
			BasicBlk blk = (BasicBlk)insertNodeToBlk.get(node);
			if(node.opCode==Op.SET) insertNewNode(node.makeCopy(env.lir),blk,blk.instrList().last());
			else{
				node = insertNewPhi(node,blk);
				if(node==null)return false;
				blk.instrList().first().addBefore(node.makeCopy(env.lir));
			}
			blkToNewNode.put(blk, node);
		}
		newNodesNumbering();
		return true;
	}
	
	
	public void insertNewNode(LirNode node, BasicBlk blk, BiLink p){
		p.addBefore(node);
		insertNodeToBlk.put(node, blk);
	}
	
	
	public LirNode insertNewPhi(LirNode phi, BasicBlk blk){
		for(int j=1;j<phi.nKids();j++){
			BasicBlk pred = (((LirLabelRef) phi.kid(j).kid(1)).label).basicBlk();
			int predVal = blkVal[pred.id];
			LirNode predVar = getVar(predVal,pred,null);
			if(predVar==null){
				insertNodeToBlk.put(phi, blk);
				return null;
			}
			phi.kid(j).setKid(0, predVar);
		}
		LirNode copy = phi.makeCopy(env.lir);
		insertNodeToBlk.put(copy, blk);
		return copy;
	}


	public void newNodesNumbering(){
		boolean change = true;
		HashSet newValNode = new HashSet();
		while(change){
			change = false;
			for(int i=0;i<newNodes.size();i++){
				LirNode node = (LirNode)newNodes.get(i);
				if(newValNode.contains(node))continue;
				BasicBlk blk = (BasicBlk)insertNodeToBlk.get(node);
				int val = gvn.getValue(node.kid(0));
				LirNode ve = gvn.makeVExp(node,blk);
				int newVal = gvn.getValue(ve);
				if(val!=-1 && val==newVal)continue;
				if(newVal==-1){
					newVal = gvn.newValue();
					newValNode.add(node);
				}
				gvn.removeValue(node.kid(0), ve, val, blk);
				gvn.setValue(newVal,node.kid(0),ve,blk);
				if(node.opCode==Op.PHI && newVal<gvn.getMaximumValue())change = true; 
			}
		}
	}
	
	
	public void cancel(LirNode var, BasicBlk blk){
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
			if(node.opCode!=Op.PHI && node.opCode!=Op.SET)continue;
			if(node.kid(0).equals(var))p.unlink();
		}
	}
	
	
	public void cancelInsertNode(){
		for(int i=0;i<newNodes.size();i++){
			LirNode node = (LirNode)newNodes.get(i);
			if(!insertNodeToBlk.containsKey(node)) continue;
			BasicBlk blk = (BasicBlk)insertNodeToBlk.get(node);
			LirNode var = node.kid(0);
			int val = gvn.getValue(var);
			gvn.removeValue(val,node.kid(0),blk);
			cancel(var,blk);
		}
	}
}
