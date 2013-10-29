/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.DFST;
import coins.backend.ana.Dominators;
import coins.backend.ana.LoopAnalysis;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirIconst;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirNode;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

/**
 *  Global Value Numbering.
 **/
public class GVN implements LocalTransformer {
	public boolean doIt(Data data, ImList args) {return true;}
	public String name() {return "GVN";}
	public String subject() {return "GVN";}
	public static final int THR = SsaEnvironment.OptThr;
	/** The threshold of debug print **/
	public static final int THR2 = SsaEnvironment.AllThr;
	private SsaEnvironment env;
	private Function f;
	
	/**
	 * Constructor.
	 * 
	 * @param env The environment of the SSA module
	 * @param sstab The current symbol table on SSA form
	 **/
	public GVN(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
	}
	
	public GVN(SsaEnvironment e, Function func, SsaSymTab sstab){
    	this.f = func;
    	this.env=e;
	}
	
	EMemoryAliasAnalyze alias;
	private DFST dfst;
	private Dominators dom;
	int idBound;
	private int value;
	private HashMap samePhiMap;
	private Stack worklist;
	private HashMap dependListMap;
	private HashMap dependMap;
	private HashMap valueTable;
	private HashMap constValTable;
	private HashMap blkVariableMap;
	private HashMap reachValueMap;
	private BasicBlk[] bVecInOrderOfRPost;
	
	/**
	 * Do Global Value Numbering.
	 * 
	 * @param func The current function
	 * @param args The list of options
	 **/
	public boolean doIt(Function func, ImList args) {
		f = func;
		gvn(1);
		alias.annul();
		f.flowGraph().touch();
		return (true);
	}
	
	public boolean checkReachability(int val, BasicBlk blk){
		HashSet reachValue = (HashSet)reachValueMap.get(blk);
		return reachValue.contains(val);
	}
	
	/**
	 * Do global value numbering.
	 * @param elmode: this is a elimination mode; 1 --> all redundant expressions are eliminated.
	 *                                          2 --> MEM expressions are not eliminated.
	 *                                          3 --> none of expressions which are eliminated.
	 */
	public void gvn(int elmode){
		dom = (Dominators) f.require(Dominators.analyzer);
		dfst = (DFST) f.require(DFST.analyzer);
		idBound = f.flowGraph().idBound();
		value = 0;
		constValTable = new HashMap();
		valueTable = new HashMap();
		blkVariableMap = new HashMap();
		samePhiMap = new HashMap();
		dependListMap = new HashMap();
		dependMap = new HashMap();
		reachValueMap = new HashMap();
		bVecInOrderOfRPost = dfst.blkVectorByRPost();
		alias=new EMemoryAliasAnalyze(env,f);
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			if(checkPhiArg(blk)){
				traverseDomTree(blk,true,elmode);
				checkPhiVal(blk);
			}
			numbering(blk,false,elmode);
		}
	}
	
	private void recordReachValue(BasicBlk blk){
		recordReachableValues(blk);
		for(BiLink p=dom.kids[blk.id].first();!p.atEnd();p=p.next()){
			BasicBlk kid = (BasicBlk)p.elem();
			recordReachValue(kid);
		}
	}
	
	public int getMaximumValue(){
		return value;
	}
	
	/**
	 * Generate a new value number.
	 * @return
	 */
	public int newValue(){
		value++;
		return value;
	}
	
	/**
	 * Generate a new value number to the argument exp and record an entry to the hash-map valueTable.
	 * @param exp
	 * @return
	 */
	private int newValue(LirNode exp, BasicBlk blk){
		value++;
		setValueRecordBlkVal(value,exp,blk);
		return value;
	}
	
	/**
	 * Do setValue and set value number val to hash-map variables which records value numbers in basic block blk and
	 * hash-set reachValue which records reachable value numbers from the start point of this function to this basic block.
	 * @param val
	 * @param exp
	 * @param blk
	 */
	private void setValueRecordBlkVal(int val, LirNode exp, BasicBlk blk){
		setValue(val,exp);
		HashMap variables = getBlkVariableMap(blk);
		if(variables.containsKey(val)) variables.remove(val);
		variables.put(val, exp);
		HashSet reachValue = getReachValueMap(blk);
		reachValue.add(val);
	}
	
	/**
	 * Set value number val to hash-map valueTable which records all the value numbers of variables and value expressions.
	 * @param val
	 * @param exp
	 */
	private void setValue(int val, LirNode exp){
		if(valueTable.containsKey(exp))valueTable.remove(exp);
		valueTable.put(exp, val);
		if(exp.nKids()==0 && exp.opCode!=Op.REG)constValTable.put(val, exp);
	}
	
	public void setValue(int val, LirNode lhs, LirNode rhs, BasicBlk blk){
		if(lhs.opCode==Op.MEM || rhs.nKids()==0 && rhs.opCode!=Op.REG){
			setValue(val,lhs);
			setValue(val,rhs,blk);
		}else{
			setValue(val,rhs);
			setValue(val,lhs,blk);
		}
	}
	
	public void setValue(int val, LirNode var, BasicBlk blk){
		if(var.opCode==Op.REG){
			if(!containValue(val,blk) || getVariable(val,blk).opCode!=Op.REG){
				setValueRecordBlkVal(val,var,blk);
			}else{
				for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
					LirNode node = (LirNode)p.elem();
					if(node.opCode!=Op.SET && node.opCode!=Op.PHI || node.kid(0).opCode==Op.MEM)continue;
					if(node.kid(0).opCode==Op.REG){
						if(getValue(node.kid(0))==val){
							if(node.kid(0).equals(var)) setValueRecordBlkVal(val,var,blk);
							else setValue(val,var);
							break;
						}
					}else if(getValue(node.kid(1))==val){
						setValue(val,var);
					}
				}
			}
		}else{
			if(var.nKids()==0) setValueRecordBlkVal(val,var,blk);
			else setValue(val,var);
		}
		setValue(val,var);
	}
	
	/**
	 * Return the value number of argument ve.
	 * If there is no entry of ve, this method returns -1.
	 * @param ve
	 * @return
	 */
	public int getValue(LirNode ve){
		if(ve.opCode==Op.PHI && sameArgVal(ve))return lirIntNodeToInteger(ve.kid(1));
		if(!valueTable.containsKey(ve)) return -1;
		return (Integer)valueTable.get(ve);
	}
	
	/**
	 * Remove an entry of exp from the hash-map valuTable.
	 * @param exp
	 */
	public void removeValue(LirNode var, LirNode exp, int val, BasicBlk blk){
		removeValue(val,var,blk);
		removeValue(val,exp,blk);
	}
	
	public void removeValue(int val, LirNode exp, BasicBlk blk){
		removeValueFromBlkMap(exp,val,blk);
		removeValue(exp);
	}
	
	private void removeValue(LirNode exp){
		valueTable.remove(exp);
	}
	
	public void removeValueFromBlkMap(LirNode exp, int val, BasicBlk blk){
		HashMap variables = getBlkVariableMap(blk);
		LirNode var = (LirNode)variables.get(val);
		if(exp.equals(var)){
			variables.remove(val);
		}
	}
	
	public LirNode valueNumberToVariable(LirNode ve, LirNode expr, BasicBlk blk, BiLink q){
		LirNode exp = ve.makeCopy(env.lir);
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).nKids()>0){
				LirNode sub = valueNumberToVariable(ve.kid(i),expr.kid(i),blk,q);
				if(sub==null)return null;
				exp.setKid(i, sub);
			}else if(expr.kid(i).opCode==Op.REG){
				int opVal = lirIntNodeToInteger(exp.kid(i));
				LirNode newReg = null;
				if(constValTable.containsKey(opVal)){
					newReg = (LirNode)constValTable.get(opVal);
				}else{
					newReg = getReachVar(opVal,blk,q);
				}
//				LirNode newReg = getReachVar(opVal,blk,q);
				if(newReg==null)return null;
				exp.setKid(i, newReg.makeCopy(env.lir));
			}else{
				exp.setKid(i, expr.kid(i));
			}
		}
		return exp;
	}
	
	public LirNode makeNewValueExp(LirNode ve, LirNode expr, BasicBlk blk, BasicBlk pred){
		LirNode newVE = ve.makeCopy(env.lir);
		for(int i=0;i<newVE.nKids();i++){
			if(expr.kid(i).opCode==Op.REG){
				for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
					LirNode node = (LirNode)p.elem();
					if(node.opCode!=Op.PHI)break;
					int veVal = lirIntNodeToInteger(ve.kid(i));
					int phiVal = getValue(node.kid(0));
					if(veVal!=phiVal)continue;
					boolean change = false;
					for(int j=1;j<node.nKids();j++){
						if(pred==(((LirLabelRef) node.kid(j).kid(1)).label).basicBlk()){
							int argVal = getValue(node.kid(j).kid(0));
							if(argVal==-1 && (node.kid(j).kid(0).nKids()==0 && node.kid(j).kid(0).opCode!=Op.REG)){
								argVal = newValue();
								setValue(argVal,node.kid(j).kid(0),pred);
							}
							newVE.setKid(i, env.lir.iconst(514, argVal));
							change = true;
							break;
						}
					}
					if(change) break;
				}
			}else if(expr.kid(i).nKids()>0){
				newVE.setKid(i, makeNewValueExp(ve.kid(i),expr.kid(i),blk,pred));
			}
		}
		return newVE;
	}
	
	public LirNode makeNewValueExp(LirNode ve, LirNode expr, BasicBlk succ){
		LirNode newVE = ve.makeCopy(env.lir);
		for(int i=0;i<newVE.nKids();i++){
			if(expr.kid(i).opCode==Op.REG){
				for(BiLink p=succ.instrList().first();!p.atEnd();p=p.next()){
					LirNode node = (LirNode)p.elem();
					if(node.opCode!=Op.PHI)break;
					int veVal = lirIntNodeToInteger(ve.kid(i));
					boolean change = false;
					for(int j=1;j<node.nKids();j++){
						int argVal = getValue(node.kid(j).kid(0));
						if(veVal==argVal){
							newVE.setKid(i, env.lir.iconst(514, getValue(node.kid(0))));
							change = true;
							break;
						}
					}
					if(change) break;
				}
			}else if(expr.kid(i).nKids()>0){
				newVE.setKid(i, makeNewValueExp(ve.kid(i),expr.kid(i),succ));
			}
		}
		return newVE;
	}
	
	/**
	 * Return true if there is the value number of the argument arg in this basic block blk.
	 * @param val
	 * @param blk
	 * @return
	 */
	public boolean containValue(int val, BasicBlk blk){
		HashMap blkValueMap = getBlkVariableMap(blk);
		return (blkValueMap.containsKey(val));
	}
	
	/**
	 * Get a variable corresponding to value number val if there is a variable in this basic block.
	 * @param val
	 * @param blk
	 * @return
	 */
	public LirNode getVariable(int val, BasicBlk blk){
		HashMap variables = getBlkVariableMap(blk);
		if(!variables.containsKey(val))return null;
		return (LirNode)variables.get(val);
	}
	
	public void updateBlkVariableMap(BasicBlk blk, HashMap valMap){
		blkVariableMap.remove(blk);
		blkVariableMap.put(blk, valMap);
	}
	
	public boolean reachValue(int val, BasicBlk blk){
		HashSet rv = getReachValueMap(blk);
		return rv.contains(val);
	}
	
	private void recordReachableValues(BasicBlk blk){
		HashSet reachValue = getReachValueMap(blk);
		for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
			BasicBlk pred = (BasicBlk)p.elem();
			HashSet predReachValueMap = getReachValueMap(pred);
			reachValue.addAll(predReachValueMap);
		}
		reachValueMap.put(blk, reachValue);
	}
	
	private void deleteReachableValues(BasicBlk blk){
		reachValueMap.remove(blk);
	}
	
	public void updateReachableValues(BasicBlk blk, HashSet valMap){
		HashSet reachValue = getReachValueMap(blk);
		reachValue.addAll(valMap);
		for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
			BasicBlk pred = (BasicBlk)p.elem();
			HashSet predReachValueMap = getReachValueMap(pred);
			reachValue.addAll(predReachValueMap);
		}
	}
	
	public int determineValue(LirNode node, BasicBlk blk){
		LirNode ve = makeVExp(node,blk);
		if(ve==null)return newValue(node.kid(2).kid(0),blk);
		int val = getValue(ve);
		if(val==-1) val = newValue(ve,blk);
		return val;
	}
	
	public int lirIntNodeToInteger(LirNode intconst){
		return (int)((LirIconst)intconst).value;
	}
	
	public LirNode makeVExp(LirNode node, BasicBlk blk){
		LirNode valExp = node.makeCopy(env.lir);
		if(node.opCode==Op.PHI){
			valExp.setKid(0, env.lir.iconst(514, blk.id));
			for(int i=1;i<node.nKids();i++){
				int val = getValue(node.kid(i).kid(0));
				if(node.kid(i).kid(0).opCode!=Op.REG && val==-1) val = newValue(node.kid(i),blk);
				valExp.setKid(i, env.lir.iconst(514, val));
			}
		}
		else if(node.opCode==Op.CALL){
			valExp = null;
		}
		else if(node.opCode==Op.SET){
			if(node.kid(1).nKids()==0)return node.kid(1).makeCopy(env.lir);
			valExp.setKid(1, makeVExp(valExp.kid(1),blk));
			valExp = valExp.kid(1);
		}
		else if(node.nKids()==0){
			int val = getValue(node);
			if(val==-1)val = newValue(node,blk);
			valExp = env.lir.iconst(514, val);
		}
		else{
			for(int i=0;i<node.nKids();i++){
				if(node.kid(i).nKids()>0){
					valExp.setKid(i, makeVExp(node.kid(i),blk));
				}else{
					int val = getValue(node.kid(i));
					if(val==-1)val = newValue(node.kid(i),blk);
					valExp.setKid(i, env.lir.iconst(514, val));
				}
			}
		}
		return valExp;
	}
	
	public LirNode getReachVar(int val, BasicBlk blk, BiLink q){
		LirNode lv = getLocalVar(val,blk,q);
		if(lv!=null)return lv;
		BasicBlk domBlk = blk;
		while(domBlk!=null){
			if(containValue(val,domBlk)) return getVariable(val,domBlk);
			else domBlk = dom.immDominator(domBlk);
		}
		return null;
	}
	
	public boolean dependLoopPhi(LirNode var){
		return dependMap.containsKey(var);
	}
	
	LirNode getLocalVar(int val, BasicBlk blk, BiLink q){
		LirNode var = null;
		if(q!=null){
			for(BiLink p=q;!p.atEnd();p=p.prev()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode==Op.SET){
					if(node.kid(0).opCode==Op.REG){
						if(getValue(node.kid(0))==val){
							if(node.kid(1).nKids()==0) var = node.kid(1);
							else var = node.kid(0);
							break;
						}
					}else{
						if(getValue(node.kid(1))==val){
							var = node.kid(1);
							break;
						}
					}
				}
				if(node.opCode==Op.PHI){
					if(getValue(node.kid(0))==val){
						var = node.kid(0);
						break;
					}
				}
				if(node.opCode==Op.CALL && node.kid(2).nKids()>0){
					if(getValue(node.kid(2).kid(0))==val){
						var = node.kid(2).kid(0);
						break;
					}
				}
				if(node.opCode==Op.PROLOGUE){
					for(int i=0;i<node.nKids();i++){
						if(node.kid(i).opCode==Op.REG && getValue(node.kid(i))==val){
							var = node.kid(i);
							break;
						}
					}
				}
			}
		}
		return var;
	}
	
	boolean checkPhiArg(BasicBlk blk){
		boolean ans = false;
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
			if(node.opCode!=Op.PHI)break;
			for(int i=1;i<node.nKids();i++){
				if(node.kid(i).kid(0).opCode==Op.REG && !valueTable.containsKey(node.kid(i).kid(0))){
					BasicBlk pred = (((LirLabelRef) node.kid(i).kid(1)).label).basicBlk();
					if(dom.dominates(blk, pred))ans = true;
					else return false;
				}
			}
		}
		return ans;
	}
	
	void traverseDomTree(BasicBlk blk, boolean optimistic, int elmode){
		numbering(blk,true,elmode);
		for(BiLink p=dom.kids[blk.id].first();!p.atEnd();p=p.next()){
			BasicBlk kid = (BasicBlk)p.elem();
			if(checkPhiArg(kid)){
				traverseDomTree(kid,true,elmode);
				checkPhiVal(kid);
			}
			traverseDomTree(kid,optimistic,elmode);
		}
	}
	
	private void numbering(BasicBlk blk, boolean optimistic, int elmode){
		deleteReachableValues(blk);
		HashMap localMap = new HashMap();
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
			if(node.opCode==Op.PROLOGUE){
				for(int i=0;i<node.nKids();i++){
					if(node.kid(i).opCode==Op.REG){
						int val = newValue();
						setValueRecordBlkVal(val,node.kid(i),blk);
					}
				}
			}
			if(node.opCode!=Op.PHI && node.opCode!=Op.SET && !(node.opCode==Op.CALL && node.kid(2).nKids()>0))continue;
			if(optimistic)checkDependPhi(node,blk);
			if(node.opCode==Op.PHI){
				int val = determineValue(node,blk);
				setValueRecordBlkVal(val,node.kid(0),blk);
				if(optimistic){
					HashMap variables = getBlkVariableMap(blk);
					if(variables.containsKey(val)){
						LirNode var = (LirNode)variables.get(val);
						if(samePhiMap.containsKey(var)) var = (LirNode)samePhiMap.get(var);
						samePhiMap.put(node.kid(0), var);
					}
				}
			}
			else if(node.opCode==Op.CALL){
				determineValue(node,blk);
			}
			else{
				int val = determineValue(node,blk);
				if(node.opCode==Op.SET && !optimistic){
					if(node.kid(0).opCode==Op.REG){
						if(node.kid(1).nKids()>0){
							if(localMap.containsKey(val)){
								LirNode pred = (LirNode)localMap.get(val);
								if(elmode==1 || elmode==2 && node.kid(1).opCode!=Op.MEM){
									node.setKid(1, pred);
								}
							}
							localMap.put(val,node.kid(0));
						}
					}else{
						localMap.put(val,node.kid(1));
					}
				}
				if(node.kid(0).opCode==Op.REG){
					setValueRecordBlkVal(val,node.kid(0),blk);
					if(node.kid(1).opCode==Op.INTCONST || node.kid(1).opCode==Op.FLOATCONST) setValueRecordBlkVal(val,node.kid(1),blk);
				}
				else setValue(val,makeVExp(node.kid(0),blk));
			}
		}
		recordReachableValues(blk);
	}
	
	private HashSet getReachValueMap(BasicBlk blk){
		HashSet reachValue;
		if(reachValueMap.containsKey(blk)){
			reachValue = (HashSet)reachValueMap.get(blk);
		}else{
			reachValue = new HashSet();
			reachValueMap.put(blk, reachValue);
		}
		return reachValue;
	}
	
	private boolean sameArgVal(LirNode ve){
		if(lirIntNodeToInteger(ve.kid(1))==-1)return false;
		for(int i=2;i<ve.nKids();i++){
			if(!ve.kid(i).equals(ve.kid(1))) return false;
		}
		return true;
	}
	
	private HashMap getBlkVariableMap(BasicBlk blk){
		if(!blkVariableMap.containsKey(blk)){
			HashMap bvm = new HashMap();
			blkVariableMap.put(blk, bvm);
		}
		return (HashMap)blkVariableMap.get(blk);
	}
	
	private void checkPhiVal(BasicBlk blk){
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode phi = (LirNode)p.elem();
				int val = determineValue(phi,blk);
				setValueRecordBlkVal(val,phi.kid(0),blk);
				if(!checkAssum(val,phi.kid(0))){
					reCompVal(phi.kid(0));
					change = true;
				}
			}
		}
		recordReachValue(blk);
	}
	
	private boolean checkAssum(int val, LirNode var){
		if(!samePhiMap.containsKey(var))return true;
		LirNode svar = (LirNode)samePhiMap.get(var);
		if(val == getValue(svar))return true;
		samePhiMap.remove(var);
		return false;
	}
	
	private void reCompVal(LirNode var){
		worklist = new Stack();
		worklist.push(var);
		while(!worklist.empty()){
			LirNode diffVar = (LirNode)worklist.pop();
			ArrayList list = getDependListMap(diffVar);
			for(int i=0;i<list.size();i++){
				ArrayList diff = (ArrayList)list.get(i);
				LirNode dNode = (LirNode)diff.get(0);
				BasicBlk dBlk = (BasicBlk)diff.get(1);
				LirNode dvar = dNode.kid(0);
				int newVal = determineValue(dNode,dBlk);
				setValueRecordBlkVal(newVal,dvar,dBlk);
				if(!checkAssum(newVal,dvar) && !worklist.contains(dvar)){
					worklist.push(dvar);
				}
			}
		}
	}
	
	private void checkDependPhi(LirNode node, BasicBlk blk){
		if(node.opCode==Op.PHI){
			for(int i=1;i<node.nKids();i++){
				if(checkDepend(node.kid(i).kid(0))){
					addDependList(node.kid(i).kid(0),node,blk);
					addDependMap(node.kid(0), node.kid(i).kid(0));
				}
			}
		}
		else if(node.opCode==Op.SET){
			if(node.kid(1).nKids()==0){
				if(checkDepend(node.kid(1))){
					addDependList(node.kid(1),node,blk);
					addDependMap(node.kid(0), node.kid(1));
				}
			}else{
				for(int i=0;i<node.kid(1).nKids();i++){
					if(checkDepend(node.kid(1).kid(i))){
						addDependList(node.kid(1).kid(i),node,blk);
						addDependMap(node.kid(0), node.kid(1).kid(i));
					}
				}
			}
		}
	}
	
	private void addDependMap(LirNode lhs, LirNode var){
		LirNode temp;
		if(samePhiMap.containsKey(var)) temp = var;
		else temp = (LirNode)dependMap.get(var);
		dependMap.put(lhs, temp);
	}
	
	private boolean checkDepend(LirNode var){
		return (samePhiMap.containsKey(var) || dependMap.containsKey(var));
	}
	
	private void addDependList(LirNode var, LirNode node, BasicBlk blk){
		LirNode phiVar;
		if(samePhiMap.containsKey(var)) phiVar = var;
		else phiVar = (LirNode)dependMap.get(var);
		ArrayList list = getDependListMap(phiVar);
		ArrayList subList = new ArrayList();
		subList.add(node);
		subList.add(blk);
		list.add(subList);
	}
	
	private ArrayList getDependListMap(LirNode var){
		if(!dependListMap.containsKey(var)){
			ArrayList list = new ArrayList();
			dependListMap.put(var, list);
			return list;
		}
		return (ArrayList)dependListMap.get(var);
	}
	
	public void printCFG(){
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			printBlk(blk);
		}
		System.out.println("********************");
	}
	
	public void printBlk(BasicBlk blk){
		LoopAnalysis loop = (LoopAnalysis)f.require(LoopAnalysis.analyzer);
		System.out.println("********************");
		System.out.println("blk:"+blk.label());
		System.out.println("id:"+blk.id);
		System.out.println("nestLevel:"+loop.nestLevel[blk.id]);
		for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
			LirNode node = (LirNode)q.elem();
			System.out.println("node:"+node);
			if(node.opCode==Op.SET){
				LirNode var = null;
				if(node.kid(0).opCode==Op.MEM) var = node.kid(1);
				else var = node.kid(0);
				System.out.println("val:"+getValue(var));
			}
			if(node.opCode==Op.PHI) System.out.println("val:"+getValue(node.kid(0)));
			if(node.opCode==Op.CALL && node.kid(2).nKids()>0) System.out.println("val:"+getValue(node.kid(2).kid(0)));
			if(node.opCode==Op.PROLOGUE){
				for(int i=0;i<node.nKids();i++){
					if(node.kid(i).opCode==Op.REG){
						System.out.println(node.kid(i)+":"+getValue(node.kid(i)));
					}
				}
			}
		}
		System.out.println("********************");
	}
	
	public void printValueNumber(LirNode var){
		if(!valueTable.containsKey(var)) System.out.println("there is no value number of "+var);
		else System.out.println(var+":"+valueTable.get(var));
	}
	
	public void printReachValue(BasicBlk blk){
		System.out.println("");
		System.out.println("blk:"+blk.label());
		HashSet reachValue = (HashSet)reachValueMap.get(blk);
		System.out.println(reachValue);
		System.out.println("");
	}
	
	public void printVarBlk(BasicBlk blk){
		System.out.println("");
		System.out.println("blk:"+blk.label());
		HashMap variables = getBlkVariableMap(blk);
		System.out.println(variables);
		System.out.println("");
	}
}