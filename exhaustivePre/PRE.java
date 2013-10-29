/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.ArrayList;
import java.util.Arrays;
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
 * Exhaustive Partial Redundancy Elimination
 **/
public class PRE implements LocalTransformer {
	public boolean doIt(Data data, ImList args) {return true;}
	public String name() {return "PRE";}
	public String subject() {return "PRE";}
	private String tmpSymName = "_pre";
	private SsaEnvironment env;
	private SsaSymTab sstab;
	private Function f;
	public BasicBlk[] bVecInOrderOfRPost;
	private DFST dfst;
	int idBound;
	boolean[] transp;
	boolean[] xTransp;
	boolean[] nIsSame;
	boolean[] xIsSame;
	public boolean[] nDSafe;
	public boolean[] xDSafe;
	public boolean[] nUSafe;
	public boolean[] xUSafe;
	public boolean[] nEarliest;
	public boolean[] xEarliest;
	public boolean[] nDelayed;
	public boolean[] xDelayed;
	public boolean[] nLatest;
	public boolean[] xLatest;
	public boolean[] nIsolated;
	public boolean[] xIsolated;
	public boolean[] nInsert;
	public boolean[] xInsert;
	public boolean[] nReplace;
	public boolean[] xReplace;
	public static final String PRE = "_pre";

	/**
	 * Constructor.
	 * 
	 * @param env The environment of the SSA module
	 * @param sstab The current symbol table on SSA form
	 **/
	public PRE(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
		this.sstab = sstab;
	}
	
	
	public PRE(SsaEnvironment env, SsaSymTab sstab, Function f) {
		this.env = env;
		this.sstab = sstab;
		this.f = f;
	}
	
	
	/**
	 * Do exhaustive PRE.
	 * 
	 * @param func The current function
	 * @param args The list of options
	 **/
	public boolean doIt(Function func, ImList args) {
		f = func;
		env.println("****************** doing exhaustive PRE to " + f.symbol.name, SsaEnvironment.MinThr);
		invoke();
		f.flowGraph().touch();
		return (true);
	}
	
	
	public void init(){
		dfst = (DFST) f.require(DFST.analyzer);
		idBound = f.flowGraph().idBound();
		bVecInOrderOfRPost = dfst.blkVectorByRPost();
	}
	
	
	public void localCM(LirNode expr, ArrayList vars, BasicBlk blk, BiLink p){
		for(BiLink q=p.prev();!q.atEnd();q=q.prev()){
			LirNode node = (LirNode)q.elem();
			if(isKill(expr.kid(1),node,vars,blk,p))break;
			if(node.opCode!=Op.SET)continue;
			ArrayList nvars = new ArrayList();
			collectVars(nvars,node);
			if(nvars.contains(expr.kid(0)))break;
			if(node.kid(1).equals(expr.kid(1))) expr.setKid(1, node.kid(0).makeCopy(env.lir));
		}
	}
	
	
	public boolean isLoad(LirNode node){
		return (node.opCode==Op.SET && node.kid(0).opCode==Op.REG && node.kid(1).opCode==Op.MEM);
	}
	
	
	public void localCodeMotion(){
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode!=Op.SET || node.kid(1).nKids()==0)continue;
				ArrayList vars = new ArrayList();
				collectVars(vars,node.kid(1));
				localCM(node,vars,blk,p);
			}
		}
	}
	
	
	private void invoke(){
		init();
		localCodeMotion();
		globalCodeMotion();
	}
	
	
	private void globalCodeMotion(){
		ArrayList insertNode = new ArrayList();
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode!=Op.SET || node.kid(1).nKids()==0 || insertNode.contains(node.kid(1)) || !checkType(node))continue;
				insertNode.add(node.kid(1).makeCopy(env.lir));
				ArrayList vars = new ArrayList();
				collectVars(vars,node.kid(1));
				pre(node,vars);
				LirNode newNode = insertNewNode(node,vars);
				if(newNode!=null) replace(newNode);
			}
		}
	}
	
	
	public void pre(LirNode node, ArrayList vars){
		compLocalProperty(node.kid(1),vars);
		compDSafe();
		compUSafe();
		compEarliest();
		compDelayed();
		compLatest();
		compIsolated();
		compInsert();
		compReplace();
	}
	
	
	public void compLocalProperty(LirNode exp, ArrayList vars){
		nIsSame = new boolean[idBound];
		xIsSame = new boolean[idBound];
		transp = new boolean[idBound];
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			transp[blk.id] = compTransp(exp,vars,blk);
			nIsSame[blk.id] = compNIsSame(exp,vars,blk);
			xIsSame[blk.id] = compXIsSame(exp,vars,blk);
		}
	}
	
	
	private boolean compNIsSame(LirNode exp, ArrayList vars, BasicBlk blk){
		for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p))break;
			if(node.opCode==Op.SET && node.kid(1).equals(exp))return true;
		}
		return false;
	}
	
	
	private boolean compXIsSame(LirNode exp, ArrayList vars, BasicBlk blk){
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p))break;
			if(node.opCode==Op.SET && node.kid(1).equals(exp))return true;
		}
		return false;
	}
	
	
	private boolean compTransp(LirNode exp, ArrayList vars, BasicBlk blk){
		for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
			LirNode node = (LirNode)p.elem();
			if(isKill(exp,node,vars,blk,p)) return false;
		}
		return true;
	}
	

	public void compDSafe() {
		nDSafe = new boolean[idBound];
		xDSafe = new boolean[idBound];
		Arrays.fill(nDSafe, true);
		Arrays.fill(xDSafe, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean x = false;
				if(xIsSame[blk.id]) x = true;
				else if(blk!=f.flowGraph().exitBlk()){
					x = true;
					for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
						BasicBlk succ = (BasicBlk)q.elem();
						if(!nDSafe[succ.id]){
							x = false;
							break;
						}
					}
				}
				boolean n = nIsSame[blk.id] || x && transp[blk.id];
				if(nDSafe[blk.id]!=n || xDSafe[blk.id]!=x) change = true;
				nDSafe[blk.id] = n;
				xDSafe[blk.id] = x;
			}
		}
	}
	
	
	public void compUSafe() {
		nUSafe = new boolean[idBound];
		xUSafe = new boolean[idBound];
		Arrays.fill(nUSafe, true);
		Arrays.fill(xUSafe, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean n = false;
				if(blk!=f.flowGraph().entryBlk()){
					n = true;
					for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
						BasicBlk pred = (BasicBlk)q.elem();
						if(!xUSafe[pred.id]){
							n = false;
							break;
						}
					}
				}
				boolean x = xIsSame[blk.id] || n && transp[blk.id];
				if(nUSafe[blk.id]!=n || xUSafe[blk.id]!=x) change = true;
				nUSafe[blk.id] = n;
				xUSafe[blk.id] = x;
			}
		}
	}
	
	
	public void compEarliest() {
		nEarliest = new boolean[idBound];
		xEarliest = new boolean[idBound];
		Arrays.fill(nEarliest, true);
		Arrays.fill(xEarliest, true);
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			boolean n = nUSafe[blk.id] || nDSafe[blk.id];
			if(n && blk!=f.flowGraph().entryBlk()){
				n = false;
				for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
					BasicBlk pred = (BasicBlk)q.elem();
					if(!(xUSafe[pred.id] || xDSafe[pred.id])){
						n = true;
						break;
					}
				}
			}
			nEarliest[blk.id] = n;
			xEarliest[blk.id] = xDSafe[blk.id] && (!transp[blk.id] || !nDSafe[blk.id] && !n);
		}
	}
	
	
	public void compDelayed() {
		nDelayed = new boolean[idBound];
		xDelayed = new boolean[idBound];
		Arrays.fill(nDelayed, true);
		Arrays.fill(xDelayed, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean n = false;
				if(nEarliest[blk.id]) n = true;
				else if(blk!=f.flowGraph().entryBlk()){
					n = true;
					for(BiLink q=blk.predList().first();!q.atEnd();q=q.next()){
						BasicBlk pred = (BasicBlk)q.elem();
						if(!xDelayed[pred.id] || xIsSame[pred.id]){
							n = false;
							break;
						}
					}
				}
				boolean x = xEarliest[blk.id] || (n && !nIsSame[blk.id]);
				if(nDelayed[blk.id]!=n || xDelayed[blk.id]!=x) change = true;
				nDelayed[blk.id] = n;
				xDelayed[blk.id] = x;
			}
		}
	}
	
	
	public void compLatest() {
		nLatest = new boolean[idBound];
		xLatest = new boolean[idBound];
		for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
			BasicBlk blk = (BasicBlk)p.elem();
			boolean x = false;
			if(xDelayed[blk.id]){
				if(xIsSame[blk.id]) x = true;
				else if(blk!=f.flowGraph().exitBlk()){
					for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
						BasicBlk succ = (BasicBlk)q.elem();
						if(!nDelayed[succ.id]){
							x = true;
							break;
						}
					}
				}
			}
			xLatest[blk.id] = x;
			nLatest[blk.id] = nDelayed[blk.id] && (!xDelayed[blk.id] || nIsSame[blk.id]);
		}
	}
	
	
	public void compIsolated(){
		nIsolated = new boolean[idBound];
		xIsolated = new boolean[idBound];
		Arrays.fill(nIsolated, true);
		Arrays.fill(xIsolated, true);
		boolean change = true;
		while(change){
			change = false;
			for(BiLink p=f.flowGraph().basicBlkList.last();!p.atEnd();p=p.prev()){
				BasicBlk blk = (BasicBlk)p.elem();
				boolean x = true;
				if(blk!=f.flowGraph().exitBlk()){
					for(BiLink q=blk.succList().first();!q.atEnd();q=q.next()){
						BasicBlk succ = (BasicBlk)q.elem();
						if(nEarliest[succ.id] || nIsSame[succ.id] || !nIsolated[succ.id]){
							x = false;
							break;
						}
					}
				}
				boolean n = !transp[blk.id] || !nIsSame[blk.id] && (xEarliest[blk.id] || x);
				if(nIsolated[blk.id]!=n || xIsolated[blk.id]!=x) change = true;
				xIsolated[blk.id] = x;
				nIsolated[blk.id] = n;
			}
		}
	}
	
	
	public void compInsert(){
		nInsert = new boolean[idBound];
		xInsert = new boolean[idBound];
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			nInsert[blk.id] = nLatest[blk.id] && !nIsolated[blk.id];
			xInsert[blk.id] = xLatest[blk.id] && !xIsolated[blk.id];
		}
	}
	
	
	public void compReplace(){
		nReplace = new boolean[idBound];
		xReplace = new boolean[idBound];
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			nReplace[blk.id] = nIsSame[blk.id] && !(nLatest[blk.id] && nIsolated[blk.id]);
			xReplace[blk.id] = xIsSame[blk.id] && !(xLatest[blk.id] && xIsolated[blk.id]);
		}
	}
	
	
	private LirNode makeNewNode(LirNode node){
		LirNode newOp = env.lir.symRef(Op.REG, node.type, sstab.newSsaSymbol(tmpSymName,node.kid(0).type) ,ImList.Empty);
		LirNode newNode = node.makeCopy(env.lir);
		newNode.setKid(0, newOp);
		return newNode;
	}
	
	
	public LirNode getNewNode(LirNode newNode, LirNode expr){
		if(newNode==null) return makeNewNode(expr).makeCopy(env.lir);
		else return newNode.makeCopy(env.lir);
	}
	
	
	public LirNode insertNewNode(LirNode expr, ArrayList vars){
		expr = expr.makeCopy(env.lir);
		LirNode newNode = null;
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			if(nInsert[blk.id]){
				boolean insert = false;
				for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
					LirNode node = (LirNode)p.elem();
					if(isKill(expr.kid(1),node,vars,blk,p))break;
					if(node.opCode==Op.SET &&node.kid(1).equals(expr.kid(1))){
						newNode = getNewNode(newNode,expr);
						p.addBefore(newNode);
						node.setKid(1, newNode.kid(0).makeCopy(env.lir));
						insert = true;
						break;
					}
				}
				if(!insert){
					newNode = getNewNode(newNode,expr);
					for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
						LirNode node = (LirNode)p.elem();
						if(node.opCode!=Op.PROLOGUE){
							p.addBefore(newNode);
							break;
						}
					}
					
				}
			}
			if(xInsert[blk.id]){
				newNode = getNewNode(newNode,expr);
				blk.instrList().last().addBefore(newNode);
			}
		}
		return newNode;
	}
	
	
	public void replace(LirNode newNode){
		for(int i=1;i<bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = bVecInOrderOfRPost[i];
			if(nReplace[blk.id]){
				for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
					LirNode node = (LirNode)p.elem();
					if(node.equals(newNode))break;
					if(node.opCode!=Op.SET || !node.kid(1).equals(newNode.kid(1)))continue;
					node.setKid(1, newNode.kid(0).makeCopy(env.lir));
					break;
				}
			}
			if(xReplace[blk.id]){
				for(BiLink p=blk.instrList().last();!p.atEnd();p=p.prev()){
					LirNode node = (LirNode)p.elem();
					if(node.equals(newNode))break;
					if(node.opCode!=Op.SET || !node.kid(1).equals(newNode.kid(1)))continue;
					node.setKid(1, newNode.kid(0).makeCopy(env.lir));
					break;
				}
			}	
		}
	}
	
	
	public boolean isKill(LirNode expr, LirNode node, ArrayList vars, BasicBlk blk, BiLink p){
		if(node.opCode==Op.CALL)return true;
		if(expr.opCode==Op.MEM && node.kid(0).opCode==Op.MEM)return true;
		if(vars.contains(node.kid(0)))return true;
		return false;
	}
	
	
	public void collectVars(ArrayList vars, LirNode exp){
		for(int i=0;i<exp.nKids();i++){
			if(exp.kid(i).opCode==Op.REG) vars.add(exp.kid(i).makeCopy(env.lir));
			else if(exp.kid(i).nKids()>0) collectVars(vars,exp.kid(i));
		}
	}
	
	
	public boolean checkType(LirNode exp){
		char type=Type.toString(exp.type).charAt(0);
		return (type=='I' || type=='F');
	}
	
	
	public void printLocalProp(LirNode expr) {
		System.out.println("----------------------------------------------------");
		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			System.out.println("blk: " + blk.label());
			System.out.println("id: " + blk.id);
			System.out.println("Transp: " + transp[blk.id]);
			System.out.println("nIsSame: " + nIsSame[blk.id]+", xIsSame:"+xIsSame[blk.id]);
			System.out.println("----------------------------------------------------");
		}
		System.out.println("target -- " + expr);
		System.out.println("");
	}
	
	
	public void printGlobalProp(LirNode expr) {
		System.out.println("----------------------------------------------------");
		for (BiLink p = f.flowGraph().basicBlkList.first(); !p.atEnd(); p = p.next()) {
			BasicBlk blk = (BasicBlk) p.elem();
			System.out.println("blk: " + blk.label());
			System.out.println("id: " + blk.id);
			System.out.println("NDSafe: " + nDSafe[blk.id] + ", XDSafe: "+ xDSafe[blk.id]);
			System.out.println("NUSafe: " + nUSafe[blk.id] + ", XUSafe: "+ xUSafe[blk.id]);
			System.out.println("NEarliest: " + nEarliest[blk.id]+ ", XEarliest: " + xEarliest[blk.id]);
			System.out.println("NDelayed: " + nDelayed[blk.id] + ", XDelayed: "+ xDelayed[blk.id]);
			System.out.println("NLatest: " + nLatest[blk.id] + ", XLatest: "+ xLatest[blk.id]);
			System.out.println("NIsolated: " + nIsolated[blk.id] + ", XIsolated: "+ xIsolated[blk.id]);
			System.out.println("NInsert: " + nInsert[blk.id]+", XInsert:"+xInsert[blk.id]);
			System.out.println("NReplace: " + nReplace[blk.id]+", XReplace:"+xReplace[blk.id]);
			System.out.println("----------------------------------------------------");
		}
		System.out.println("target -- " + expr);
		System.out.println("");
	}
}