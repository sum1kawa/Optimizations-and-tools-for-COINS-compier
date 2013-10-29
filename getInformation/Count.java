/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */

package coins.ssa;

import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.DominanceFrontiers;
import coins.backend.ana.LoopAnalysis;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

/**
 * 
 *  get some information.
 *
 */
public class Count implements LocalTransformer {
	public boolean doIt(Data data, ImList args) {return true;}
	public String name() {return "COUNT";}
	public String subject() {return "COUNT";}

	public static final int THR = SsaEnvironment.OptThr;
	/** The threshold of debug print **/
	public static final int THR2 = SsaEnvironment.AllThr;
	private Function f;
	BasicBlk[] bVecInOrderOfRPost;
	EMemoryAliasAnalyze alias;
	private LoopAnalysis loop;
	DominanceFrontiers df;
	private SsaEnvironment env;


	/**
	 * Constructor
	 * 
	 * @param e The environment of the SSA module
	 * @param tab The symbol tabel of the SSA module
	 * @param function The current function
	 * @param m The current mode
	 **/
	public Count(SsaEnvironment e, SsaSymTab tab) {
		env = e;
		env.println(" Effective Demand Driven Patial Redundancy Elimination on SSA form", SsaEnvironment.MsgThr);
	}
	
	public Count(Function function) {
		f = function;
	}

	
	void countExp(){
		int expNum = 0;
		int loadExp = 0;
		int storeExp = 0;
		int memExp = 0;
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
				LirNode node = (LirNode)q.elem();
				expNum++;
				if(node.opCode==Op.SET){
					if(node.kid(0).opCode==Op.MEM){
						storeExp++;
						memExp++;
					}else if(node.kid(1).opCode==Op.MEM){
						loadExp++;
						memExp++;
					}
				}
			}
		}
		System.out.println("");
		System.out.println("exp num:"+expNum);
		System.out.println("mem exp:"+memExp);
		System.out.println("load exp:"+loadExp);
		System.out.println("store exp:"+storeExp);
	}
	
	
	public void coindLoad(){
		int num = 0;
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
				LirNode node = (LirNode)q.elem();
				if(node.opCode==Op.SET && node.kid(1).opCode==Op.MEM){
					num++;
				}
			}
		}
		System.out.println("number of load statements is "+num);
	}
	
	public void countLoadInLoop(){
		int num = 0;
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			if(loop.nestLevel[blk.id]==0) continue;
			for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
				LirNode node = (LirNode)q.elem();
				if(node.opCode==Op.SET && node.kid(1).opCode==Op.MEM){
					num++;
				}
			}
		}
		System.out.println("number of load statements in loop is "+num);
	}
	
	
	public boolean doIt(Function function, ImList args) {
		f = function;
		countExp();
		return (true);
	}
}

