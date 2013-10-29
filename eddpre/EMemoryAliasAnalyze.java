/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Op;
import coins.backend.Type;
import coins.backend.util.ImList;
import coins.backend.Function;
import coins.backend.lir.LirNode;
import coins.backend.util.BiLink;
import coins.backend.util.BiList;
import coins.backend.cfg.BasicBlk;
import coins.backend.ana.Dominators;
import coins.backend.ana.DominanceFrontiers;

import java.util.Hashtable;
import java.util.Stack;

/**
 * Analyze the aliases of memory object.<br>
 * The SSA module have a preliminary alias analysis.
 * This alias analyze regard the whole memory place as a single object.
 * Therefore, any stores to the memory make it dirty.
 * The SSA module translate the single memory object to SSA form.
 * The way to translate is the same as for abstract registers. But the phi
 * functions are not inserted. On the marge point of the control flow,
 * the compiler make a new name for the single memory object.
 **/
class EMemoryAliasAnalyze{
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The current function **/
  private Function f;
  /** The work stack **/
  private Stack stack;
  /** The dominator object **/
  private Dominators dom;
  /** Utility **/
  private Util util;
  /** The next number of assignment to the memory object **/
  private long nextNum;
  /** Number of the count about assignment to the memory object **/
  public boolean[] offset;
  /** The rank of the exit of the basic blocks **/
  private long[] blkRankOut;
  /** The rank of the entry of the basic blocks **/
  private long[] blkRankIn;
  /** The map for CALL node **/
  private Hashtable callMap;

  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param function The current function
   **/
  EMemoryAliasAnalyze(SsaEnvironment e,Function function){
    f=function;
    env=e;
    nextNum=0;
    callMap=new Hashtable();
    stack=new Stack();

    // initialize the rank of basic block
    blkRankOut=new long[f.flowGraph().idBound()];
    blkRankIn=new long[f.flowGraph().idBound()];
    for(int i=0;i<f.flowGraph().idBound();i++){
      blkRankOut[i]=nextNum;
      blkRankIn[i] = nextNum;
    }

    // Push the bottom number to the stack.
    stack.push(env.lir.iconst(Type.UNKNOWN,nextNum++,ImList.Empty));

    // Make a utility object.
    util=new Util(env,f);
    // Make a dominator object.
    dom=(Dominators)f.require(Dominators.analyzer);

    setOffset();
    markMem(f.flowGraph().entryBlk());

    f.touch();
//    f.printIt(env.output);
  }

  /**
   * Return the rank of the specified basic block.
   * @param blk The specified basic block
   * @return The rank of the specified basic block
   **/
  long blkRankOut(BasicBlk blk){
    return(blkRankOut[blk.id]);
  }

  long blkRankIn(BasicBlk blk){
    return(blkRankIn[blk.id]);
  }

  /**
   * If find the assignment to the memory object, increment the offset
   * counter in the dominance frontier of the current basic block.
   * This is same as translating program from the normal form to the SSA form.
   **/
  private void setOffset(){
    offset=new boolean[f.flowGraph().idBound()];
    DominanceFrontiers df;
    df=(DominanceFrontiers)f.require(DominanceFrontiers.analyzer);

    for(int i=0;i<offset.length;i++) offset[i]=false;

    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        // If find the assignment to the memory object.
        if((node.opCode==Op.SET && node.kid(0).opCode==Op.MEM) ||
           node.opCode==Op.CALL){
          for(BiLink r=df.frontiers[blk.id].first();!r.atEnd();r=r.next()){
            BasicBlk frontier=(BasicBlk)r.elem();
            markFrontier(frontier);
          }
          break;
        }
      }
    }
  }

  /**
   * Mark up the dominance frontieres of the specified basic block.
   * @param blk The specified basic block
   **/
  private void markFrontier(BasicBlk blk){
    if(offset[blk.id]==true) return;
    offset[blk.id]=true;

    // mark dominance frontiers recursively.
    DominanceFrontiers df;
    df=(DominanceFrontiers)f.require(DominanceFrontiers.analyzer);
    for(BiLink r=df.frontiers[blk.id].first();!r.atEnd();r=r.next()){
      BasicBlk frontier=(BasicBlk)r.elem();
      markFrontier(frontier);
    }
  }

  /**
   * Return the threshold of the CALL node.
   * The threshold is to check whether the CALL node can be put
   * into the list of LIR nodes.
   * @param call The current CALL node
   * @return The threshold of the CALL node
   **/
  long callThreshold(LirNode call){
    if(call.opCode!=Op.CALL) return(-1);

    Long callID=new Long(call.id);
//    env.output.println("LLLLLLLLLLLLLLL "+callID);
    Long val=(Long)callMap.get(callID);
    if(val==null) return(-1);
      
    return(val.longValue());
  }

  /**
   * Mark the number to the momery object.
   * @param blk The current basic block
   **/
  private void markMem(BasicBlk blk){
    int count=0;

    if(offset[blk.id]){
      LirNode suffix=env.lir.iconst(Type.UNKNOWN,nextNum++,ImList.Empty);
      count++;
      stack.push(suffix);
    }

    blkRankIn[blk.id]=nextNum-1;

    for(BiLink p=blk.instrList().first();!p.atEnd();p=p.next()){
      LirNode node=(LirNode)p.elem();
      if(node.opCode!=Op.PHI && node.opCode!=Op.PROLOGUE){
        // If the current node is a assign node, mark the number which 
        // are only right hand side of the node.
        // If the current node is not a assign node, mark the number
        // in whole of the statement.
        switch(node.opCode){
          case Op.CALL:{
            replaceMem(node.kid(0),node,0);
            replaceMem(node.kid(1),node,1);
            if(node.kid(2).nKids()>0 && node.kid(2).kid(0).opCode==Op.MEM)
              replaceMem(node.kid(2).kid(0).kid(0),node.kid(2).kid(0),0);
            else
              replaceMem(node.kid(2),node,2);

            callMap.put(new Long(node.id),new Long(nextNum));
            LirNode suffix=env.lir.iconst(Type.UNKNOWN,nextNum++,
                                          ImList.Empty);
            stack.push(suffix);
            count++;

            break;
          }
          case Op.SET:{
            if(node.kid(0).opCode==Op.MEM){
              replaceMem(node.kid(0).kid(0),node.kid(0),0);
            }
            replaceMem(node.kid(1),node,1);
            break;
          }
          default:{
            replaceMem(node,null,0);
          }
        }
      }
      // If the assignment to the memory object is found, 
      // increment the counter.
      if(node.opCode==Op.PROLOGUE){
        for(int i=1;i<node.nKids();i++){
          if(node.kid(i).opCode==Op.MEM){
            LirNode suffix=env.lir.iconst(Type.UNKNOWN,nextNum++,ImList.Empty);
            count++;
            LirNode copyNode=node.kid(i).kid(0).makeCopy(env.lir);
            LirNode newMem=env.lir.operator(Op.MEM,node.kid(i).type,
                                            copyNode,suffix,node.kid(i).opt);
            node.setKid(i,newMem);
            stack.push(suffix);
          }
        }
      }
      else if((node.opCode==Op.SET && node.kid(0).opCode==Op.MEM) ||
              (node.opCode==Op.CALL && node.kid(2).nKids()>0 &&
               node.kid(2).kid(0).opCode==Op.MEM)){
        LirNode suffix=env.lir.iconst(Type.UNKNOWN,nextNum++,ImList.Empty);
        count++;
        if(node.opCode==Op.SET){
          LirNode copyNode=node.kid(0).kid(0).makeCopy(env.lir);
          LirNode newMem=env.lir.operator(Op.MEM,node.kid(0).type,
                                          copyNode,suffix,node.kid(1).opt);
          node.setKid(0,newMem);
        }
        else{ // CALL
          LirNode copyNode=node.kid(2).kid(0).kid(0).makeCopy(env.lir);
          LirNode newMem=env.lir.operator(Op.MEM,node.kid(2).kid(0).type,
                                          copyNode,suffix,
                                          node.kid(2).kid(0).opt);
          node.kid(2).setKid(0,newMem);
        }
        stack.push(suffix);
      }
    }

    blkRankOut[blk.id]=nextNum-1;
//    env.output.println("blk "+blk.id+" --> "+blkRankOut[blk.id]);

    // Mark recursively.
    for(BiLink p=dom.kids[blk.id].first();!p.atEnd();p=p.next()){
      markMem((BasicBlk)p.elem());
    }

    // Pop from stack.
    if(count>0){
      for(int i=0;i<count;i++) stack.pop();
    }
  }

  /**
   * Marking method. The number to the memory object is the top of the stack.
   * This method change the MEM nodes to the SSA specific ones.
   * MUST annuling after optimization.
   * @param root The current LIR node
   * @param parent The parent node of the current LIR node
   * @param place The number which kid of the parent
   **/
  private void replaceMem(LirNode root,LirNode parent,int place){
    if(root!=null){
      for(int i=0;i<root.nKids();i++){
        replaceMem(root.kid(i),root,i);
      }
      if(parent!=null && root.opCode==Op.MEM){
        LirNode suffix=(LirNode)stack.peek();
        LirNode newMem=env.lir.operator(Op.MEM,root.type,root.kid(0),
                                        suffix.makeCopy(env.lir),
                                        root.opt);
        env.println("MAA : "+root+" ---> "+newMem,SsaEnvironment.AllThr);
        parent.setKid(place,newMem);
        root=newMem;
      }
    }
  }
  
  public LirNode getIndex(BasicBlk blk){
	  return env.lir.iconst(Type.UNKNOWN,blkRankOut[blk.id],ImList.Empty);
  }
  
  
  public LirNode makeNewMem(LirNode root){
	  LirNode suffix=env.lir.iconst(Type.UNKNOWN,nextNum++,ImList.Empty);
	  return env.lir.operator(Op.MEM,root.type,root.kid(0),
              suffix.makeCopy(env.lir),
              root.opt);
  }

  /**
   * Annuling the information about the alias analysis from all the 
   * memory object. This method MUST be called after optmizing useing
   * the information about the alias analysis.
   **/
  void annul(){
    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        memAsBefore(node,null,0);
      }
    }
    f.touch();
  }

  /**
   * Remove the information about alias analysis from the MEM node.
   * @param root The current LIR node
   * @param parent The parent node of the current LIR node
   * @param place The number which kid of the parent
   **/
  private void memAsBefore(LirNode root,LirNode parent,int place){
    if(root!=null){
      if(parent!=null && root.opCode==Op.MEM){
        LirNode newMem=env.lir.operator(Op.MEM,root.type,root.kid(0),
                                        root.opt);
        env.println("MAA : annul "+newMem,SsaEnvironment.AllThr);
        parent.setKid(place,newMem);
        root=newMem;
      }
      for(int i=0;i<root.nKids();i++){
        memAsBefore(root.kid(i),root,i);
      }
    }
  }
}
