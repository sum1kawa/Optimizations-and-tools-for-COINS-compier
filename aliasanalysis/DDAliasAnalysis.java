/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.HashSet;
import java.util.HashMap;
import java.util.ArrayList;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.Dominators;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;
import coins.backend.lir.LirLabelRef;
import coins.backend.lir.LirNode;

class DDAliasAnalysis implements LocalTransformer {
  /** The output stream of the compiler **/
    private SsaEnvironment env;
    public static final int THR=SsaEnvironment.OptThr;
    private Function f;
    private Dominators dom;
    private int idBound;
    private HashMap blkToAmbSet;
    private HashMap blkToAlias;
    private ArrayList phiCongruenceClass;
    
    public DDAliasAnalysis(SsaEnvironment e,Function func){
    	f = func;
    	env=e;
    	idBound = func.flowGraph().idBound();
    	dom = (Dominators) f.require(Dominators.analyzer);
    	makeMayAliasGroup();
    	makeCongruenceClass();
    }
    public DDAliasAnalysis(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
	}
    
    
    private void makeCongruenceClass(){
    	phiCongruenceClass = new ArrayList();
    	for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
    		BasicBlk blk = (BasicBlk)p.elem();
    		for(BiLink pp=blk.instrList().first();!pp.atEnd();pp=pp.next()){
    			LirNode phi = (LirNode)pp.elem();
    			if(phi.opCode!=Op.PHI)continue;
    			makePhiCC(phi);
    		}
    	}
    }
    
    
    public void makePhiCC(LirNode phi){
    	HashSet newCC = new HashSet();
		for(int i=1;i<phi.nKids();i++){
			HashSet cc = getCC(phi.kid(i).kid(0));
			if(cc!=null)newCC.addAll(cc);
			newCC.add(phi.kid(i).kid(0));
		}
		HashSet defCC = getCC(phi.kid(0));
		if(defCC!=null) newCC.addAll(defCC);
		newCC.add(phi.kid(0));
		phiCongruenceClass.add(newCC);
    }
    
    
    private HashSet getCC(LirNode var){
    	HashSet temp = null;
    	for(int i=0;i<phiCongruenceClass.size();i++){
    		HashSet cc = (HashSet)phiCongruenceClass.get(i);
    		if(cc.contains(var)){
    			temp = cc;
    			phiCongruenceClass.remove(cc);
    			break;
    		}
    	}
    	return temp;
    }
    
    
    private boolean checkCongruence(LirNode var1, LirNode var2){
    	HashSet var1CC = getCC(var1);
    	return (var1CC!=null && var1CC.contains(var2));
    }
    
    
    private HashMap getAliasSet(BasicBlk blk){
    	if(!blkToAlias.containsKey(blk)){
    		HashMap nodeToAlias = new HashMap(blk.instrList().length());
    		blkToAlias.put(blk, nodeToAlias);
    	}
    	return (HashMap)blkToAlias.get(blk);
    }
    
    
    private HashSet getAmbAliasSet(BasicBlk blk){
    	if(!blkToAmbSet.containsKey(blk)){
    		HashSet ambToAmbSet = new HashSet();
    		blkToAmbSet.put(blk, ambToAmbSet);
    	}
    	return (HashSet)blkToAmbSet.get(blk);
    }
    
    
    private void makeMayAliasGroup(){
    	blkToAmbSet = new HashMap();
    	blkToAlias = new HashMap();
    	for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
    		BasicBlk blk = (BasicBlk)p.elem();
    		makeMayAliasGroup(blk);
    	}
    }
    
    
    private void makeMayAliasGroup(BasicBlk blk){
    	HashMap nodeToAlias = getAliasSet(blk);
		HashSet ambSet = getAmbAliasSet(blk);
		for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
			LirNode node = (LirNode)q.elem();
			if(node.opCode==Op.PROLOGUE){
				for(int i=0;i<node.nKids();i++){
					if(node.kid(i).opCode==Op.REG) ambSet.add(node.kid(i));
				}
			}
			if(node.opCode==Op.SET) insertNewEntry(node,blk,nodeToAlias,ambSet);
			if(node.opCode==Op.CALL) getAmbSet(node,ambSet);
		}
    }
    
    
    private HashSet getAliases(LirNode var, HashMap nodeToAlias){
    	if(!nodeToAlias.containsKey(var)){
    		HashSet addrs = new HashSet();
    		nodeToAlias.put(var, addrs);
    	}
    	return (HashSet)nodeToAlias.get(var);
    }
    
    
    private void insertNewEntry(LirNode set, BasicBlk blk, HashMap nodeToAlias, HashSet ambSet){
    	LirNode laddr = getAddr(set.kid(0));
		LirNode raddr = getAddr(set.kid(1)); 
		setAmbSet(laddr,raddr,blk,ambSet);
		HashSet addrs = getAliases(laddr,nodeToAlias);
		addrs.add(laddr);
		addrs.add(raddr);
		if(nodeToAlias.containsKey(raddr)){
			HashSet predSet = (HashSet)nodeToAlias.get(raddr);
			addrs.addAll(predSet);
		}
		if(set.kid(0).opCode==Op.REG && !isAmb(raddr,blk)) ambSet.remove(laddr);
    }
    
    
    public void insertNewEntry(LirNode set, BasicBlk blk){
    	HashMap nodeToAlias = getAliasSet(blk);
		HashSet ambSet = getAmbAliasSet(blk);
		insertNewEntry(set,blk,nodeToAlias,ambSet);
    }
    
    
    private void setAmbSet(LirNode addr1, LirNode addr2, BasicBlk blk, HashSet ambSet){
		ambSet.add(addr1);
		ambSet.add(addr2);
		for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
			BasicBlk pred = (BasicBlk)p.elem();
			HashSet predAmbSet = getAmbAliasSet(pred);
			if(predAmbSet.contains(addr1) || predAmbSet.contains(addr2)) ambSet.addAll(predAmbSet);
		}
    }
    
    
    private boolean isAmb(LirNode addr, BasicBlk blk){
    	HashSet ambSet = getAmbAliasSet(blk);
    	return (addr.opCode==Op.STATIC || ambSet.contains(addr));
    }
    
    
    private void getAmbSet(LirNode exp, HashSet ambSet){
    	for(int i=0;i<exp.nKids();i++){
    		if(exp.kid(i).opCode==Op.REG) ambSet.add(exp.kid(i));
    		else if(exp.kid(i).nKids()>0) getAmbSet(exp.kid(i),ambSet);
    	}
    }
    
    
    public boolean checkAlias(LirNode load, LirNode store, BasicBlk blk, BiLink q){
    	if(load.opCode!=Op.MEM || store.opCode!=Op.MEM){
    		System.out.println("Error @ check demand-driven alias analysis");
    		return true;
    	}
    	LirNode addr1 = getAddr(load);
    	LirNode addr2 = getAddr(store);
    	if(addr1.equals(addr2))return true;
    	if(addr1.opCode==Op.STATIC && addr2.opCode==Op.STATIC)return true;
    	if(addr1.opCode==Op.FRAME && addr2.opCode==Op.FRAME)return false;
    	int ans = checkLocal(addr1,addr2,blk,q);
    	if(ans==1)return true;
    	return (checkGlobal(addr1,addr2,blk));
    }
    
    public void collectVars(ArrayList vars, LirNode exp){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG) vars.add(exp.kid(i).makeCopy(env.lir));
			else if(exp.kid(i).nKids()>0) collectVars(vars,exp.kid(i));
		}
	}
    
    /**
     * If this method returns true, the load and the store are alias.
     * @param load
     * @param store
     * @param blk
     * @param q
     * @return
     */
    public boolean checkAliasSSA(LirNode load, LirNode store, BasicBlk blk, BiLink q, ArrayList loadVars){
    	if(load.opCode!=Op.MEM || store.opCode!=Op.MEM){
    		System.out.println("Error @ check demand-driven alias analysis");
    		return true;
    	}
    	if(load.equals(store))return true;
    	LirNode addr1 = getAddr(load);
    	LirNode addr2 = getAddr(store);
    	if(addr1.opCode==Op.STATIC && addr2.opCode==Op.STATIC)return true;
    	if(addr1.opCode==Op.FRAME && addr2.opCode==Op.FRAME)return false;
    	return true;
//    	if(checkCongruence(addr1,addr2))return true;
//    	ArrayList newAddr = new ArrayList();
//    	newAddr.add(addr2);
//    	boolean[] visited = new boolean[idBound];
//    	int ans = checkLocalSSA(addr1,blk,q,newAddr,visited);
//    	if(ans==1) return true;
//    	return (checkGlobalSSA(addr1,blk,q,newAddr,visited));
    }
    
    public boolean checkAliasSSA(LirNode load, LirNode store, BasicBlk blk, BiLink q){
    	if(load.opCode!=Op.MEM || store.opCode!=Op.MEM){
    		System.out.println("Error @ check demand-driven alias analysis");
    		return true;
    	}
    	LirNode addr1 = getAddr(load);
    	LirNode addr2 = getAddr(store);
    	
    	if(addr1.equals(addr2))return true;
    	if(addr1.opCode==Op.STATIC && addr2.opCode==Op.STATIC)return true;
    	if(addr1.opCode==Op.FRAME && addr2.opCode==Op.FRAME)return false;
    	return true;
//    	if(checkCongruence(addr1,addr2))return true;
//    	ArrayList newAddr = new ArrayList();
//    	newAddr.add(addr2);
//    	boolean[] visited = new boolean[idBound];
//    	int ans = checkLocalSSA(addr1,blk,q,newAddr,visited);
//    	if(ans==1) return true;
//    	return (checkGlobalSSA(addr1,blk,q,newAddr,visited));
    }
    
    
    private boolean checkGlobalSSA(LirNode loadAddr, BasicBlk blk, BiLink q, ArrayList newAddr, boolean[] visited){
    	BasicBlk domBlk = blk;
    	while(true){
    		visited[domBlk.id] = true;
    		if(checkLocalSSA(loadAddr,domBlk,q,newAddr,visited)==1) return true;
    		else{
    			domBlk = dom.immDominator(domBlk);
    			if(domBlk==null)break;
    			q = domBlk.instrList().last();
    		}
    	}
    	return false;
    }
    
    
    private boolean contain(LirNode var, LirNode exp){
    	if(exp.equals(var)) return true;
    	else{
    		for(int i=0;i<exp.nKids();i++){
    			if(exp.kid(i).equals(var) || exp.kid(i).nKids()>0 && contain(var,exp.kid(i))) return true;
    		}
    	}
    	return false;
    }
    
    
    /**
     * 
     * return value ans: 1 is true;
     *                   2 is false;
     *                   0 cannot determine the answer.
     * 
     * @param loadAddr
     * @param blk
     * @param q
     * @param newAddr
     * @return
     */
    private int checkLocalSSA(LirNode loadAddr, BasicBlk blk, BiLink q, ArrayList newAddr, boolean[] visited){
    	LirNode storeAddr = (LirNode)newAddr.get(0);
    	for(BiLink p=q;!p.atEnd();p=p.prev()){
    		LirNode node = (LirNode)p.elem();
    		if(node.opCode==Op.PROLOGUE){
    			for(int i=0;i<node.nKids();i++){
    				if(node.kid(i).equals(loadAddr) || node.kid(i).equals(storeAddr))return 1;
    			}
    			return 2;
    		}
    		if(node.opCode==Op.PHI && node.kid(0).equals(storeAddr)){
    			for(int i=1;i<node.nKids();i++){
    				BasicBlk pred = (((LirLabelRef) node.kid(i).kid(1)).label).basicBlk();
    				if(newAddr.contains(node.kid(i).kid(0)) || visited[pred.id])continue;
    				newAddr.add(0, node.kid(i).kid(0));
    				if(checkGlobalSSA(loadAddr,pred,pred.instrList().last(),newAddr,visited)) return 1;
    				newAddr.remove(node.kid(i).kid(0));
    			}
    			return 2;
    		}
    		if(node.opCode==Op.SET){
    			LirNode addr = getAddr(node.kid(0));
    			if(node.kid(0).opCode==Op.MEM){
    				if((isAmb(loadAddr,blk) && isAmb(storeAddr,blk)) && isAmb(addr,blk)) return 1;
    			}
    			if(node.kid(0).equals(storeAddr)){
    				if(node.kid(1).opCode==Op.REG && !newAddr.contains(node.kid(1))){
    					storeAddr = node.kid(1);
    					newAddr.add(0,storeAddr);
    					continue;
    				}
    				if(contain(loadAddr,node.kid(1))) return 1;
    				else return 2;
    			}
    		}
    		if(node.opCode==Op.CALL){
    			if(mayAmb(loadAddr,node) && mayAmb(storeAddr,node) || (isAmb(loadAddr,blk) && isAmb(storeAddr,blk))) return 1;
    		}
    	}
    	return 0;
    }
 
 
    /**
     *  It return 0: It could not determine the answer.
     *            1: alias.
     *            2: not alias.
     */
    private int checkLocal(LirNode loadAddr, LirNode storeAddr, BasicBlk blk, BiLink q){
    	for(BiLink p=q;!p.atEnd();p=p.prev()){
    		LirNode node = (LirNode)p.elem();
    		if(node.opCode==Op.PROLOGUE){
    			for(int i=0;i<node.nKids();i++){
    				if(node.kid(i).equals(loadAddr) || node.kid(i).equals(storeAddr))return 1;
    			}
    			return 2;
    		}
    		if(node.opCode==Op.SET){
    			LirNode addr = getAddr(node.kid(0));
    			if(node.kid(0).opCode==Op.MEM){
    				if((isAmb(loadAddr,blk) && isAmb(storeAddr,blk)) && isAmb(addr,blk)) return 1;
    			}
    			if(alias(addr,storeAddr,blk,q)){
    				if(alias(getAddr(node.kid(1)),loadAddr,blk,q) || node.kid(1).nKids()>0 && loadAddr.equals(getAddr(node.kid(1)))) return 1;
    				else return 2;
    			}
    		}
    		if(node.opCode==Op.CALL){
    			if(mayAmb(loadAddr,node) && mayAmb(storeAddr,node) || (isAmb(loadAddr,blk) && isAmb(storeAddr,blk))) return 1;
    		}
    	}
    	return 0;
    }
    
    
    private boolean mayAmb(LirNode addr, LirNode exp){
    	for(int i=0;i<exp.nKids();i++){
    		if(exp.kid(i).equals(addr) || exp.kid(i).nKids()>0 && mayAmb(addr,exp.kid(i))) return true;
    	}
    	return false;
    }
    
    
    private boolean alias(LirNode raddr, LirNode load, BasicBlk blk, BiLink q){
    	for(BiLink p=blk.instrList().first();p!=q;p=p.next()){
    		LirNode node = (LirNode)p.elem();
    		if(node.opCode==Op.CALL && mayAmb(raddr,node))return true;
    		if(node.opCode!=Op.SET || !node.kid(0).equals(raddr))continue;
    		if(getAddr(node.kid(1)).equals(load))return true;
    	}
    	for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
    		BasicBlk pred = (BasicBlk)p.elem();
    		HashSet ambSet = getAmbAliasSet(pred);
    		if(ambSet.contains(raddr))return true;
    	}
    	return false;
    }
    
    
    private boolean checkGlobal(LirNode loadAddr, LirNode storeAddr, BasicBlk blk){
    	boolean[] visited = new boolean[idBound];
    	return checkGlobal(loadAddr,storeAddr,blk,visited);
    }
    
    
    private boolean checkGlobal(LirNode loadAddr, LirNode storeAddr, BasicBlk blk, boolean[] visited){
    	visited[blk.id] = true;
    	for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
    		BasicBlk pred = (BasicBlk)p.elem();
    		if(visited[pred.id])continue;
    		int ans = checkLocal(loadAddr,storeAddr,pred,pred.instrList().last());
        	if(ans==1)return true;
        	if(ans==2)continue;
    		if(checkGlobal(loadAddr,storeAddr,pred,visited)) return true;
    	}
    	return false;
    }
    
    
    private LirNode getAddr(LirNode mem){
    	if(mem.nKids()==0) return mem;
    	else if(mem.kid(0).nKids()==0) return mem.kid(0);
    	else return getAddr(mem.kid(0));
    }
    
    
    public boolean doIt(Function func, ImList args) {
		f = func;
		env.println("****************** doing DDCPYP to " + f.symbol.name, SsaEnvironment.MinThr);
		f.flowGraph().touch();
		return (true);
	}

	/**
	 * @param data Data to be processes.
	 * @param args List of optional arguments.
	 **/
	public boolean doIt(Data data, ImList args) {return true;}
	/**
	 * Return the name of this optimizer.
	 **/
	public String name() {return "DDAliasAnalysis";}
	/**
	 * Return brief descriptions of this optimizer.
	 **/
	public String subject() {return "DDAliasAnalysis";}
}