/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.LocalTransformer;
import coins.backend.Op;
import coins.backend.ana.LoopAnalysis;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.util.BiLink;
import coins.backend.util.ImList;

/**
 * Print all of BasicBlk and nodes.
 **/
public class Print implements LocalTransformer {
	public boolean doIt(Data data, ImList args) {return true;}
	public String name() {return "Print";}
	public String subject() {return "Print";}
	public static final int THR = SsaEnvironment.OptThr;
	/** The threshold of debug print **/
	public static final int THR2 = SsaEnvironment.AllThr;
	private Function f;

	/**
	 * Constructor.
	 * 
	 * @param env The environment of the SSA module
	 * @param sstab The current symbol table on SSA form
	 **/
	public Print(SsaEnvironment env, SsaSymTab sstab) {}
	
	public Print(SsaEnvironment e,Function func){
    	f = func;
    }
	
	public void printAll(){
		LoopAnalysis loop = (LoopAnalysis)f.require(LoopAnalysis.analyzer);
		for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
			BasicBlk blk = (BasicBlk)p.elem();
			System.out.println("********************");
			System.out.println("blk:"+blk.label());
			System.out.println("nestLevel:"+loop.nestLevel[blk.id]);
			System.out.println("id:"+blk.id);
			for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
				LirNode node = (LirNode)q.elem();
				System.out.println("node:"+node);
			}
		}
		System.out.println("********************");
	}
	
	public void printBlk(BasicBlk blk){
		System.out.println("********************");
		System.out.println("blk:"+blk.label());
		for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
			LirNode node = (LirNode)q.elem();
			System.out.println("node:"+node);
		}
		System.out.println("********************");
	}
	
	public void print(LirNode node){
		switch(node.opCode){
		case(Op.INTCONST):
		case(Op.FLOATCONST):
		case(Op.MEM):
		case(Op.REG):{
			System.out.println("var:"+node);
			break;
		}
		default:{
			System.out.println("node:"+node);
		}
		}
	}
	
	public void print(BasicBlk blk){
		System.out.println("blk:"+blk.label());
	}
	
	public void newNode(LirNode node){
		System.out.println("new node:"+node);
	}
	
	
	public void phi(LirNode phi){
		System.out.println("phi:"+phi);
	}
	
	
	/**
	 * Do Print all of BasicBlk and nodes.
	 * 
	 * @param func The current function
	 * @param args The list of options
	 **/
	public boolean doIt(Function func, ImList args) {
		f = func;
		printAll();
		f.flowGraph().touch();
		return (true);
	}
}
