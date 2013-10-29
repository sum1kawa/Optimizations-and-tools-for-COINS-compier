/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.Dominators;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.util.ImList;
import coins.backend.lir.LirNode;

import java.util.Arrays;
import java.util.Stack;
import java.util.ArrayList;
import java.util.HashMap;

class DDCPYP implements LocalTransformer {
  /** The output stream of the compiler **/
    private SsaEnvironment env;
    public static final int THR=SsaEnvironment.OptThr;
    private Function f;
    private Dominators dom;
    public DDCPYP(SsaEnvironment e,Function func){
    	f = func;
    	env=e;
    }
    public DDCPYP(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
	}
    
    // for data flow equation
    private boolean[] checked;
    private BiList subTree;
    private boolean[] kill;
    private boolean[] nAvail;
    private boolean[] xAvail;
    private HashMap blkToUseList;
    private HashMap expToVar;
    private HashMap varToExp;
    private ArrayList varList;
    private HashMap blkToExpToVarMap;
    private HashMap blkToVarToExpMap;
    private HashMap blkToVarList;
    // for question propagation
    boolean visited[];
    boolean result[];
    
    
    public boolean doIt(Function func, ImList args) {
		f = func;
		env.println("****************** doing DDCPYP to " + f.symbol.name, SsaEnvironment.MinThr);
		invoke();
		f.flowGraph().touch();
		return (true);
	}
    
    
    private void invoke(){
    	int mode = 0; // 0 -> use data flow equation. 1 -> use question propagation.
    	for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
    		BasicBlk blk = (BasicBlk)p.elem();
    		for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
    			LirNode node = (LirNode)q.elem();
    			if(node.opCode!=Op.SET || node.kid(0).opCode!=Op.REG || node.kid(1).nKids()>0)continue;
    			boolean global = true;
				// local copy propagation.
				for(BiLink pp=q.next();!pp.atEnd();pp=pp.next()){
					LirNode n = (LirNode)pp.elem();
					if(!cpyp(n,node.kid(0),node.kid(1))){
						global = false;
						break;
					}
				}
				if(global) cpyp(blk,node.kid(0),node.kid(1),mode);
    		}
    	}
    }
    
    
    /**
     * This method is for DDPRE.
     * @param blk
     * @return
     */
    public void cpyp(BasicBlk blk, LirNode from, LirNode to, BiLink p, int mode, HashMap blkToExpToVarMap, HashMap blkToVarToExpMap, HashMap blkToVarList){
    	if(blkToExpToVarMap!=null){
    		this.blkToExpToVarMap = blkToExpToVarMap;
    		this.blkToVarToExpMap = blkToVarToExpMap;
    		this.blkToVarList = blkToVarList;
    		setMap(blk);
    	}
    	boolean global = true;
    	for(BiLink q=p.next();!q.atEnd();q=q.next()){
			LirNode n = (LirNode)q.elem();
			if(!cpyp(n,from,to)){
				global = false;
				break;
			}
		}
    	if(global)cpyp(blk,from,to,mode);
    }
    
    
    public void cpyp(BasicBlk blk, LirNode from, LirNode to, BiLink p, int mode){
    	boolean global = true;
    	for(BiLink q=p.next();!q.atEnd();q=q.next()){
			LirNode n = (LirNode)q.elem();
			if(!cpyp(n,from,to)){
				global = false;
				break;
			}
		}
    	if(global)cpyp(blk,from,to,mode);
    }
    
    
    /**
     * It is necessary that do local copy propagation before call this method.
     * @param blk
     * @param from
     * @param to
     */
    public void cpyp(BasicBlk blk, LirNode from, LirNode to, int mode){
    	dom = (Dominators) f.require(Dominators.analyzer);
    	if(from.nKids()!=0 && to.nKids()!=0){
    		System.out.println("Error");
    		System.out.println("can not "+from+" -> "+to);
    		System.exit(1);
    	}
    	if(mode==0) doItByDataFlowEquation(blk,from,to);
		else doItByQuestionPropagation(blk,from,to);
    }
    
    
    public boolean cpyp(LirNode node, LirNode from, LirNode to){
    	to = to.makeCopy(env.lir);
    	switch(node.opCode){
    	case(Op.SET):{
    		int posVarList = -1;
			boolean remove = false;
    		if(expToVar!=null && expToVar.containsKey(node.kid(1))){
    			remove = true;
    			LirNode var = (LirNode)expToVar.get(node.kid(1));
    			posVarList = varList.indexOf(var);
    			varToExp.remove(var);
    			varList.remove(var);
    			expToVar.remove(node.kid(1));
    		}
    		if(node.kid(1).nKids()==0){
    			if(node.kid(1).equals(from)) node.setKid(1, to.makeCopy(env.lir));
    		}else cpyp(node.kid(1),from,to);
    		if(node.kid(0).equals(from) || node.kid(0).equals(to)) return false;
    		if(node.kid(0).nKids()>0) cpyp(node.kid(0),from,to);
    		if(remove){
    			LirNode copy = node.makeCopy(env.lir);
    			varToExp.put(copy.kid(0), copy.kid(1));
    			if(posVarList>-1)varList.add(posVarList, copy.kid(0));
    			expToVar.put(copy.kid(1), copy.kid(0));
    		}
    		break;
    	}
    	case(Op.CALL):{
    		int posVarList = -1;
    		if(varList!=null && varList.contains(node)){
    			posVarList = varList.indexOf(node);
    			varList.remove(posVarList);
    		}
    		cpyp(node.kid(0),from,to);
			cpyp(node.kid(1),from,to);
    		if(node.kid(2).nKids()>0){
    			if(node.kid(2).kid(0).equals(from) || node.kid(2).kid(0).equals(to)) return false;
    			if(node.kid(2).kid(0).nKids()>0) cpyp(node.kid(2).kid(0),from,to);
    		}
    		if(posVarList>-1)varList.add(posVarList, node.makeCopy(env.lir));
    		break;
    	}
    	default:{
    		for(int i=0;i<node.nKids();i++){
    			if(node.kid(i).equals(from)) node.setKid(i, to.makeCopy(env.lir));
    			if(node.kid(i).nKids()>0) cpyp(node.kid(i),from,to);
    		}
    	}
    	}
    	return true;
    }
    
    
    /**
     * It is necessary that do local copy propagation before call this method.
     * @param blk
     * @param from
     * @param to
     */
    private void doItByQuestionPropagation(BasicBlk blk, LirNode from, LirNode to){
		blkToUseList = new HashMap();
		visited = new boolean[f.flowGraph().idBound()];
		result = new boolean[f.flowGraph().idBound()];
		kill = new boolean[f.flowGraph().idBound()];
		Arrays.fill(visited, false);
		Arrays.fill(result, false);
		Arrays.fill(kill, false);
    	visited[blk.id] = true;
    	result[blk.id] = true;
    	qp(blk,blk,from,to);
    	change(blk,from,to);
    }
    
    
    /**
     * Check each blocks in control flow graph contain LirNode which have "from" variable and kill "from" or "to" variables.
     * If exist kill expression in loop, assumption that all of blocks in the loop kill "from" or "to" variables.
     * @param top
     * @param blk
     * @param from
     * @param to
     */
    private boolean qp(BasicBlk top, BasicBlk blk, LirNode from, LirNode to){
    	for(BiLink p=dom.kids[blk.id].first();!p.atEnd();p=p.next()){
    		BasicBlk kid = (BasicBlk)p.elem();
    		if(!checkTransp(blk,kid,from,to)) return false;
    		ArrayList useList = new ArrayList();
    		for(BiLink q=kid.instrList().first();!q.atEnd();q=q.next()){
    			LirNode node = (LirNode)q.elem();
    			if(checkUse(node,from)) useList.add(node);
    			if(kill(node,from,to)){
    				blkToUseList.put(kid, useList);
    				return false;
    			}
    		}
    		blkToUseList.put(kid, useList);
    		if(!qp(top,kid,from,to)) break;
    	}
    	return true;
    }
    
    
    private void change(BasicBlk blk, LirNode from, LirNode to){
    	Stack blks = new Stack();
    	boolean[] checked = new boolean[f.flowGraph().idBound()];
    	blks.push(blk);
    	while(!blks.empty()){
    		BasicBlk b = (BasicBlk)blks.pop();
    		if(!result[b.id] || checked[b.id]) continue;
    		checked[b.id] = true;
    		for(BiLink p=b.succList().first();!p.atEnd();p=p.next()){
    			BasicBlk succ = (BasicBlk)p.elem();
    			if(blkToExpToVarMap!=null)setMap(succ);
    			if(!result[succ.id] && !kill[succ.id])continue;
    			blks.push(succ);
    			ArrayList useList = (ArrayList)blkToUseList.get(succ);
    			if(useList==null) continue;
    			for(int i=0;i<useList.size();i++){
    				LirNode node = (LirNode)useList.get(i);
    				cpyp(node,from,to);
    			}
    		}
    	}
    }
    
    
    /**
     * It is necessary that do local copy propagation before call this method.
     * @param blk
     * @param from
     * @param to
     */
    private void doItByDataFlowEquation(BasicBlk blk, LirNode from, LirNode to){
    	blkToUseList = new HashMap();
    	kill = new boolean[f.flowGraph().idBound()];
        nAvail = new boolean[f.flowGraph().idBound()];
        xAvail = new boolean[f.flowGraph().idBound()];
        Arrays.fill(nAvail, true);
        Arrays.fill(xAvail, true);
    	createSubTree(blk);
    	compLocalProp(blk,from,to);
    	compAvail();
    	change(from,to);
    }
    
    
    /**
     * To create sub-CFG.
     * @param e
     */
    private void addBlk(BasicBlk e){
    	Stack blks = new Stack();
    	blks.add(e);
    	while(!blks.empty()){
    		BasicBlk blk = (BasicBlk)blks.pop();
    		for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
    			BasicBlk pred = (BasicBlk)p.elem();
    			if(pred==e || checked[pred.id]) continue;
    			checked[pred.id] = true;
    			subTree.add(pred);
    			blks.push(pred);
    		}
    	}
    }
    
    
    private void createSubTree(BasicBlk blk){
    	subTree = new BiList();
    	subTree.add(blk);
    	checked = new boolean[f.flowGraph().idBound()];
    	Arrays.fill(checked, false);
    	checked[blk.id] = true;
    	Stack blks = new Stack();
    	blks.push(blk);
    	while(!blks.empty()){
    		BasicBlk b = (BasicBlk)blks.pop();
    		if(!checked[b.id]){
    			subTree.add(b);
    			checked[b.id] = true;
    		}
    		for(BiLink p=dom.kids[b.id].first();!p.atEnd();p=p.next()){
        		BasicBlk kid = (BasicBlk)p.elem();
        		if(checked[kid.id]) continue;
        		subTree.add(kid);
        		checked[kid.id] = true;
        		addBlk(kid);
        		blks.push(kid);
        	}
    	}
    }
    
    
    private boolean checkUse(LirNode exp, LirNode from){
    	if(exp.equals(from)) return true;
    	for(int i=0;i<exp.nKids();i++){
    		if(exp.kid(i).equals(from) || exp.kid(i).nKids()>0 && checkUse(exp.kid(i),from)) return true;
    	}
    	return false;
    }
    
    
    private void compLocalProp(BasicBlk checkBlk, LirNode from, LirNode to){
    	for(BiLink p=subTree.first();!p.atEnd();p=p.next()){
    		BasicBlk blk = (BasicBlk)p.elem();
    		if(blk==checkBlk)continue;
    		ArrayList useList = new ArrayList();
    		for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
    			LirNode node =(LirNode)q.elem();
    			if(node.opCode==Op.SET){
    				if(checkUse(node.kid(1),from)) useList.add(node);
    				if(node.kid(0).equals(from) || node.kid(0).equals(to)){
    					kill[blk.id] = true;
    					break;
    				}
    				if(!useList.contains(node) && checkUse(node.kid(0),from)) useList.add(node);
    			}
    			if(node.opCode==Op.CALL){
    				if(checkUse(node.kid(0),from) || checkUse(node.kid(1),from)) useList.add(node);
    				if(node.kid(2).nKids()>0){
    					if(node.kid(2).kid(0).equals(from) || node.kid(2).kid(0).equals(to)){
    						kill[blk.id] = true;
        					break;
    					}
    					if(checkUse(node.kid(2).kid(0),from)) useList.add(node);
    				}
    			}
    			if(checkUse(node,from)) useList.add(node);
    		}
    		blkToUseList.put(blk, useList);
    	}
    }
    
    
    private void compAvail(){
    	boolean change = true;
    	while(change){
    		change = false;
    		for(BiLink p=subTree.first();!p.atEnd();p=p.next()){
        		BasicBlk blk = (BasicBlk)p.elem();
        		boolean n = true;
        		for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
        			BasicBlk pred = (BasicBlk)q.elem();
        			if(!xAvail[pred.id]){
    					n = false;
    					break;
    				}
        		}
        		boolean x = n && !kill[blk.id];
        		if(nAvail[blk.id]!=n || xAvail[blk.id]!=x){
        			xAvail[blk.id] = x;
        			nAvail[blk.id] = n;
        			change = true;
        		}
        	}
    	}
    }
    
    
    private void change(LirNode from, LirNode to){
    	for(BiLink p=subTree.first();!p.atEnd();p=p.next()){
    		BasicBlk blk = (BasicBlk)p.elem();
    		if(!nAvail[blk.id])continue;
    		ArrayList useList = (ArrayList)blkToUseList.get(blk);
    		if(useList!=null){
    			for(int i=0;i<useList.size();i++){
    				LirNode node = (LirNode)useList.get(i);
    				cpyp(node,from,to);
    			}
    		}
    	}
    }
    
    
    private boolean checkTransp(BasicBlk top, BasicBlk kid, LirNode from, LirNode to){
    	boolean[] visited = new boolean[f.flowGraph().idBound()]; 
    	for(BiLink p=top.succList().first();!p.atEnd();p=p.next()){
    		BasicBlk succ = (BasicBlk)p.elem();
    		if(succ==kid || visited[succ.id]) continue;
    		if(!checkTransp(succ,kid,from,to,visited)) return false;
    	}
    	return true;
    }
    
    
    private boolean checkTransp(BasicBlk blk, BasicBlk dst, LirNode from, LirNode to, boolean[] visited){
    	visited[blk.id] = true;
    	for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
    		LirNode node = (LirNode)p.elem();
    		if(kill(node,from,to)) return false;
    	}
    	for(BiLink p=blk.succList().first();!p.atEnd();p=p.next()){
    		BasicBlk succ = (BasicBlk)p.elem();
    		if(succ==dst || visited[succ.id]) continue;
    		if(!checkTransp(succ,dst,from,to,visited)) return false;
    	}
    	return true;
    }
    
    
    private boolean kill(LirNode node, LirNode from, LirNode to){
    	if(node.opCode==Op.SET && (node.kid(0).equals(from) || node.kid(0).equals(to))) return true;
		if(node.opCode==Op.CALL && node.kid(2).nKids()>0 && (node.kid(2).kid(0).equals(from) || node.kid(2).kid(0).equals(to))) return true;
		return false;
    }
    
    
    /**
     * This method is for DDPRE.
     * @param blk
     * @return
     */
    private void setMap(BasicBlk blk){
    	expToVar = (HashMap)blkToExpToVarMap.get(blk);
    	varToExp = (HashMap)blkToVarToExpMap.get(blk);
    	varList = (ArrayList)blkToVarList.get(blk);
    }
    
    
	/**
	 * @param data Data to be processes.
	 * @param args List of optional arguments.
	 **/
	public boolean doIt(Data data, ImList args) {return true;}
	/**
	 * Return the name of this optimizer.
	 **/
	public String name() {return "DDCPYP";}
	/**
	 * Return brief descriptions of this optimizer.
	 **/
	public String subject() {return "DDCPYP";}
}

