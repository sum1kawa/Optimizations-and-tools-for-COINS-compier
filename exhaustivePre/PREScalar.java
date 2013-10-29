/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import java.util.ArrayList;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;
/**
 * Exhaustive Partial Redundancy Elimination
 **/
public class PREScalar implements LocalTransformer {
	public boolean doIt(Data data, ImList args) {return true;}
	public String name() {return "PRE";}
	public String subject() {return "PRE";}
	private SsaEnvironment env;
	private SsaSymTab sstab;
	private Function f;
	PRE pre;

	/**
	 * Constructor.
	 * 
	 * @param env The environment of the SSA module
	 * @param sstab The current symbol table on SSA form
	 **/
	public PREScalar(SsaEnvironment env, SsaSymTab sstab) {
		this.env = env;
		this.sstab = sstab;
	}
	
	public PREScalar(SsaEnvironment env, SsaSymTab sstab, Function f) {
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
		env.println("****************** doing exhaustive PRE whose target is scalar only to " + f.symbol.name, SsaEnvironment.MinThr);
		invoke();
		f.flowGraph().touch();
		return (true);
	}
	
	
	private void invoke(){
		pre = new PRE(env,sstab,f);
		pre.init();
		localCM();
		globalCM();
	}
	
	void localCM(){
		for(int i=1;i<pre.bVecInOrderOfRPost.length; i++) {
			BasicBlk blk = pre.bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode!=Op.SET || pre.isLoad(node) || node.kid(1).nKids()==0)continue;
				ArrayList vars = new ArrayList();
				pre.collectVars(vars,node.kid(1));
				pre.localCM(node,vars,blk,p);
			}
		}
	}
	
	
	void globalCM(){
		for(int i=1;i<pre.bVecInOrderOfRPost.length; i++) {
			ArrayList insertNode = new ArrayList();
			BasicBlk blk = pre.bVecInOrderOfRPost[i];
			for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
				LirNode node = (LirNode)p.elem();
				if(node.opCode!=Op.SET || pre.isLoad(node) || node.kid(1).nKids()==0 || insertNode.contains(node.kid(1)) || !pre.checkType(node))continue;
				insertNode.add(node.kid(1).makeCopy(env.lir));
				ArrayList vars = new ArrayList();
				pre.collectVars(vars,node.kid(1));
				pre.pre(node,vars);
				LirNode newNode = pre.insertNewNode(node,vars);
				if(newNode!=null) pre.replace(newNode);
			}
		}
	}
	
}