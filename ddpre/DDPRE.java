/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.Type;
import coins.backend.ana.DFST;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

/**
 * Demand Driven Partial Redundancy Elimination Normal Form version.
 **/
public class DDPRE implements LocalTransformer {
	private String tmpSymName = "_ddpre";
	public static final int THR = SsaEnvironment.OptThr;
	/** The threshold of debug print **/
	public static final int THR2 = SsaEnvironment.AllThr;
	private SsaEnvironment env;
	private Function f;
	
	BasicBlk[] bVecInOrderOfRPost;

	private DDCPYP ddcpyp;
	private Print print;
	//
	private DFST dfst;
	private SsaSymTab sstab;
	LirNode preTmp;
	
	boolean[] visited;
	boolean[] result;
	boolean[] killBlk;
	boolean[] isAvail;
	boolean[] isReal;
	
	int idBound;
	int exprPos;
	
	HashMap blkToVarToExpMap;
	HashMap blkToExpToVarMap;
	HashMap blkToVarList;
	LirNode newNode;
	ArrayList insertBlk;
	ArrayList insertedNode;
	ArrayList exprVars;
	LirNode expr;
	LirNode exprAddr;
	BasicBlk exprBlk;
	LirNode insertNode;
	
	ArrayList localEliminateRedundantBlks;
	
	public static final String DDPRE = "_ddpre";

	int preNum;
	
	/**
	 * Constructor.
	 * 
	 * @param env
	 *            The environment of the SSA module
	 * @param sstab
	 *            The current symbol table on SSA form
	 **/
	public DDPRE(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
		this.sstab = sstab;
		preNum = 0;
	}
	
	
	boolean checkType(LirNode exp){
		char type=Type.toString(exp.type).charAt(0);
		return (type=='I' || type=='F');
	}
	
	
	HashMap getBlkVTEMap(BasicBlk blk){
		if(!blkToVarToExpMap.containsKey(blk))initBlk(blk);
		return (HashMap)blkToVarToExpMap.get(blk);
	}
	
	
	HashMap getBlkETVMap(BasicBlk blk){
		if(!blkToExpToVarMap.containsKey(blk))initBlk(blk);
		return (HashMap)blkToExpToVarMap.get(blk);
	}
	
	
	ArrayList getBlkVarList(BasicBlk blk){
		if(!blkToVarList.containsKey(blk))initBlk(blk);
		return (ArrayList)blkToVarList.get(blk);
	}
	
	
	boolean kill(LirNode expr, LirNode node, ArrayList vars){
		if(expr.kid(1).opCode==Op.MEM){
			if(node.opCode==Op.CALL || node.opCode==Op.SET && node.kid(0).opCode==Op.MEM){
				return true;
			}
		}
		
		return node.opCode==Op.SET && vars.contains(node.kid(0)) ||
				node.opCode==Op.CALL && node.kid(2).nKids()>0 && vars.contains(node.kid(2).kid(0));
		
	}
	
	
	LirNode createNewNode(LirNode expr){
		LirNode newOp = env.lir.symRef(Op.REG, expr.type, sstab.newSsaSymbol(tmpSymName,expr.kid(0).type) ,ImList.Empty);
		LirNode newNode = expr.makeCopy(env.lir);
		newNode.setKid(0, newOp);
		return newNode;
	}
	
	
	
	void collectVars(LirNode exp, ArrayList vars){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG){
				vars.add(exp.kid(i));
			}else if(exp.kid(i).nKids()>0){
				collectVars(exp.kid(i),vars);
			}
		}
	}
	
	
	boolean eliminateLocalRedundant(LirNode n, BasicBlk blk, ArrayList vars, BiLink p){
		for(BiLink q=p.prev();!q.atEnd();q=q.prev()){
			LirNode node = (LirNode)q.elem();
			if(kill(n,node,vars)){
				break;
			}else if(node.opCode==Op.SET && node.kid(1).equals(n.kid(1))){
				n.setKid(1, node.kid(0).makeCopy(env.lir));
				if(node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.REG)
					ddcpyp.cpyp(blk,node.kid(0),node.kid(1),p,1,blkToExpToVarMap,blkToVarToExpMap,blkToVarList);
				return true;
			}
		}
		return false;
	}
	

	boolean checkTransp(LirNode expr, ArrayList vars, BiLink p){
		for(BiLink q=p.prev();!q.atEnd();q=q.prev()){
			LirNode node = (LirNode)q.elem();
			if(kill(expr,node,vars)){
				return false;
			}
		}
		return true;
	}
	
	
	void checkBlk(BasicBlk blk){
		if(!blkToVarList.containsKey(blk))initBlk(blk);
		int num=0;
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
			num++;
			if(node.opCode!=Op.SET || node.kid(1).nKids()==0 || !checkType(node))continue;
			ArrayList vars = new ArrayList();
			collectVars(node.kid(1),vars);
			if(checkTransp(node,vars,p)){
				visited = new boolean[idBound];
				result = new boolean[idBound];
				isAvail = new boolean[idBound];
				isReal = new boolean[idBound];
				Arrays.fill(isAvail, false);
				Arrays.fill(isReal, false);
				Arrays.fill(visited, false);
				Arrays.fill(result, false);
				insertBlk = new ArrayList();
				exprBlk = blk;
				exprPos = blk.instrList().length()-num+1;
				newNode = null;
				
//				System.out.println("");
//				System.out.println("*** new node ***");
//				System.out.println("");
//				System.out.println("blk:"+blk.label());
//				System.out.println("node:"+node);
//				System.out.println("vars:"+vars);
				
				if(propagate(node,blk,vars)){
					
					LirNode newNode = getNewNode(node);
					insert(node,newNode,vars);
					
					if(node.kid(1).opCode!=Op.REG){
						newNode = newNode.makeCopy(env.lir);
						replace(node,newNode,blk,p);
					}
					newNode = null;
				}
			}
		}
	}
	

	boolean propagate(LirNode node, BasicBlk blk, ArrayList vars){
		ArrayList blks = new ArrayList();
		boolean True = false;
		boolean False = false;
		boolean Real = false;
		
		if(blk!=f.flowGraph().entryBlk()){
			for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
				BasicBlk pred = (BasicBlk)p.elem();
				if(visited[pred.id]){
					if(result[pred.id]){
						if(isAvail[pred.id]){
							True = true;
							if(isReal[pred.id])Real = true;
						}else{
							False = true;
							blks.add(pred);
						}
					}else{
						True = true;
					}
				}else if(pred==exprBlk){
					result[pred.id] = true;
					boolean avail = true;
					int num=0;
					for(BiLink q=pred.instrList().last();!q.atEnd();q=q.prev()){
						LirNode n = (LirNode)q.elem();
						num++;
						if(num==exprPos){
							break;
						}
						if(kill(node,n,vars)){
							avail = false;
							break;
						}else if(n.opCode==Op.SET && n.kid(1).equals(node.kid(1))){
							insertBlk.add(pred);
							break;
						}	
					}
					if(avail){
						True = true;
						Real = true;
						isAvail[pred.id] = true;
						isReal[pred.id] = true;
					}else{
						blks.add(pred);
					}
				}else{
					if(local(node,pred,vars)){
						True = true;
						if(isReal[pred.id])Real = true;
					}else{
						False = true;
						blks.add(pred);
					}
					result[pred.id] = true;
				}
			}
		}
		
		result[blk.id] = true;
		visited[blk.id] = true;
		
		if(True){
			if(False){
				if(blks.size()==0 || !Real){
					return false;
				}
				for(int i=0;i<blks.size();i++){
					BasicBlk pred = (BasicBlk)blks.get(i);
					if(!checkAnt(node.kid(1),pred,vars)){
						return false;
					}
				}
				insertBlk.addAll(blks);
			}
			isAvail[blk.id] = true;
			if(Real)isReal[blk.id] = true;
			return true;
		}else{
			return false;
		}
	}
	
	
	boolean local(LirNode node, BasicBlk blk, ArrayList vars){
	    visited[blk.id] = true;
	    
	    HashMap expToVar = getBlkETVMap(blk);
	    ArrayList varList = getBlkVarList(blk);
	    
	    if(expToVar.containsKey(node.kid(1))){
	    	HashMap varToExp = getBlkVTEMap(blk);
	    	for(int i=(varList.size()-1);i>=0;i--){
	    		LirNode var = (LirNode)varList.get(i);
	    		if(vars.contains(var) || (node.kid(1).opCode==Op.MEM && var.opCode==Op.CALL || var.opCode==Op.MEM))break;
	    		LirNode exp = (LirNode)varToExp.get(var);
	    		if(exp!=null && exp.equals(node.kid(1))){
	    			insertBlk.add(blk);
	    			isAvail[blk.id] = true;
	    			isReal[blk.id] = true;
	    			return true;
	    		}
	    	}
	    	return false;
	    }else{
	    	if(node.kid(1).opCode==Op.MEM && killBlk[blk.id]){
	    		return false;
	    	}
	    	for(int i=0;i<vars.size();i++){
	    		LirNode var = (LirNode)vars.get(i);
	    		if(varList.contains(var)){
	    			return false;
	    		}
	    	}
	    	return propagate(node,blk,vars);
	    }
	    
	}
	
	
	void initBlk(BasicBlk blk){
		HashMap varToExp = new HashMap();
		HashMap expToVar = new HashMap();
		ArrayList varList = new ArrayList();
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
			if(node.opCode==Op.SET){
				ArrayList vars = new ArrayList();
				collectVars(node.kid(1),vars);
				if(node.kid(1).nKids()>0){
					eliminateLocalRedundant(node,blk,vars,p);
				}
			}
			recordNode(node,blk,varToExp,expToVar,varList);
		}
		
		blkToExpToVarMap.put(blk, expToVar);
		blkToVarToExpMap.put(blk, varToExp);
		blkToVarList.put(blk, varList);
		
	}
	
	
	void recordNode(LirNode node, BasicBlk blk, HashMap varToExp, HashMap expToVar, ArrayList varList){
		if(node.opCode==Op.SET){
			if(varToExp.containsKey(node.kid(0))){
				// kill
				LirNode predExp = (LirNode)varToExp.get(node.kid(0));
				varToExp.remove(node.kid(0));
				expToVar.remove(predExp);
			}
			
			LirNode copy = node.makeCopy(env.lir);
			varToExp.put(copy.kid(0), copy.kid(1));
			
			if(copy.kid(1).nKids()>0){
				expToVar.put(copy.kid(1), copy.kid(0));
			}
			
			if(varList.contains(copy.kid(0)))varList.remove(copy.kid(0));
			
			if(copy.kid(0).opCode==Op.MEM){
				killBlk[blk.id] = true;
			}
			
			varList.add(copy.kid(0));
			
		}else if(node.opCode==Op.CALL){
			killBlk[blk.id] = true;
			LirNode copy = node.makeCopy(env.lir);
			varList.add(copy);
			if(copy.kid(2).nKids()>0 && copy.kid(2).kid(0).opCode==Op.REG){
				// kill
				if(varList.contains(copy.kid(2).kid(0)))varList.remove(node.kid(2).kid(0));
				varList.add(copy.kid(2).kid(0));
			}
		}else if(node.opCode==Op.PROLOGUE){
		    for(int i=0;i<node.nKids();i++){
			if(node.kid(i).opCode==Op.REG){
			    varList.add(node.kid(i));
			}
		    }
		}
	}
	
		
	boolean checkAnt(LirNode exp, BasicBlk blk, ArrayList vars){
		boolean[] visited = new boolean[idBound];
		for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
			BasicBlk succ = (BasicBlk)p.elem();
			if(visited[succ.id] || exprBlk==succ)continue;
			if(!checkAnt(exp,succ,vars,visited))return false;
		}
		return true;
	}
	
	
	boolean checkAnt(LirNode exp, BasicBlk blk, ArrayList vars, boolean visited[]){
		HashMap expToVar = getBlkETVMap(blk);
		ArrayList varList = getBlkVarList(blk);
		boolean memExp = (exp.opCode==Op.MEM);
		visited[blk.id] = true;
		if(expToVar.containsKey(exp)){
			LirNode var = (LirNode)expToVar.get(exp);
			for(int i=0;i<varList.size();i++){
				LirNode v = (LirNode)varList.get(i);
				if(v.equals(var)){
					return true;
				}else if(vars.contains(v)){
					break;
				}else if(memExp){
					if(v.opCode==Op.CALL || v.opCode==Op.MEM){
						break;
					}
				}
			}
			return false;
		}else{
			if(memExp && killBlk[blk.id] || blk==f.flowGraph().exitBlk()){
				return false;
			}else{
				for(int i=0;i<vars.size();i++){
					LirNode var = (LirNode)vars.get(i);
					if(varList.contains(var)){
						return false;
					}
				}
				for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
					BasicBlk succ = (BasicBlk)p.elem();
					if(visited[succ.id])continue;
					if(!checkAnt(exp,succ,vars,visited)){
						return false;
					}
				}
			}
		}
		
		return true;
		
	}
	
	
	void insert(LirNode node, LirNode newNode, ArrayList vars){
		boolean[] inserted = new boolean[idBound];
		Arrays.fill(inserted, false);
		for(int i=0;i<insertBlk.size();i++){
			BasicBlk blk = (BasicBlk)insertBlk.get(i);
			if(inserted[blk.id])continue;
			boolean insert = false;
			LirNode insertNode = newNode.makeCopy(env.lir);
			
			ArrayList varList = getBlkVarList(blk);
			HashMap varToExp = getBlkVTEMap(blk);
			
			for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
				LirNode n = (LirNode)p.elem();
				if(kill(node,n,vars)){
					break;
				}else if(n.opCode==Op.SET){
					if(n.kid(1).equals(newNode.kid(1))){
						insert = true;
						p.addBefore(insertNode.makeCopy(env.lir));
						int index = varList.indexOf(n.kid(0));
						varList.add(index, insertNode.kid(0));
						replace(n,insertNode,blk,p);
						break;
					}else if(varToExp.containsKey(n.kid(0))){
						LirNode exp = (LirNode)varToExp.get(n.kid(0));
						if(exp!=null && exp.equals(newNode.kid(1))){
							insert = true;
							insertNode.setKid(1, n.kid(0).makeCopy(env.lir));
							p.addAfter(insertNode.makeCopy(env.lir));
							int index = varList.indexOf(n.kid(0));
							varList.add(index+1, insertNode.kid(0));
							break;
						}
					}
				}
			}
			
			if(!insert){
				BiLink p=blk.instrList().last();
				p.addBefore(insertNode.makeCopy(env.lir));
				varList.add(insertNode.kid(0));
			}
			
			inserted[blk.id] = true;
			HashMap expToVar = getBlkETVMap(blk);
			expToVar.put(insertNode.kid(1), insertNode.kid(0));
			varToExp.put(insertNode.kid(0), insertNode.kid(1));
		}
		insertedNode.add(newNode);
	}
	
	
	void replace(LirNode node,LirNode newNode, BasicBlk blk, BiLink p){
		if(newNode.opCode==Op.REG){
			node.setKid(1, newNode);
		}else if(newNode.opCode==Op.SET){
			node.setKid(1, newNode.kid(0));
		}
		if(node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.REG)ddcpyp.cpyp(blk,node.kid(0),node.kid(1),p,1,blkToExpToVarMap,blkToVarToExpMap,blkToVarList);
		
	}
	
	
	LirNode getNewNode(LirNode node){
		if(newNode==null){
			newNode = (createNewNode(node)).makeCopy(env.lir);
		}
		return newNode.makeCopy(env.lir);
	}
	
	
	void invoke(){
		idBound = f.flowGraph().idBound();
		killBlk = new boolean[idBound];
		Arrays.fill(killBlk, false);
		blkToExpToVarMap = new HashMap();
		blkToVarToExpMap = new HashMap();
		blkToVarList = new HashMap();
		insertedNode = new ArrayList();
		BasicBlk[] bVecInOrderOfRPost = dfst.blkVectorByRPost();
		for (int i=1;i<bVecInOrderOfRPost.length;i++) {
    	    BasicBlk blk = bVecInOrderOfRPost[i];
    	    checkBlk(blk);
		}
	}
	
	
	/**
	 * Do Demand Driven Partial Redundancy Elimination Normal Form version.
	 * 
	 * @param func
	 *            The current function
	 * @param args
	 *            The list of options
	 **/
	public boolean doIt(Function func, ImList args) {
		f = func;
		env.println("****************** doing DDPRE to " + f.symbol.name, SsaEnvironment.MinThr);
		dfst = (DFST) f.require(DFST.analyzer);
		ddcpyp = new DDCPYP(env, f);
		print = new Print(env, f);
		
//		long startTime = System.currentTimeMillis();
		
		invoke();
		
//		System.exit(1);
//		long stopTime = System.currentTimeMillis();
//		System.out.println("analyze time = "+(stopTime-startTime));
		
		f.flowGraph().touch();
		return (true);
	}
	

	/**
	 * @param data
	 *            Data to be processes.
	 * @param args
	 *            List of optional arguments.
	 **/
	public boolean doIt(Data data, ImList args) {
		return true;
	}

	/**
	 * Return the name of this optimizer.
	 **/
	public String name() {
		return "DDPRE";
	}

	/**
	 * Return brief descriptions of this optimizer.
	 **/
	public String subject() {
		return "DDPRE";
	}

}
