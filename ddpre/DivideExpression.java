/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.util.BiLink;
import coins.backend.cfg.BasicBlk;
import coins.backend.lir.LirNode;
import coins.backend.Op;
import coins.backend.util.ImList;
import coins.backend.sym.Symbol;

/**
 * Divide expressions into 3 address expression.
 **/
class DivideExpression implements LocalTransformer{ 
  public boolean doIt(Data data, ImList args) { return true; }
  public String name() { return "DivideExpression"; }
  public String subject() {
    return "Divide expression into three adress code on SSA form.";
  }

 /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The current symbol table of the SSA module **/
  private SsaSymTab sstab;
  /** The threshold of the debug print **/
  public static final int THR=SsaEnvironment.OptThr;
  /** The name of the symbol which the optimzer uses to make the temporary
      variables **/
  public static final String DIVEX="_divex";

  /**
   * Constructor
   * @param e The environment of the SSA module
   * @param symtab The current symbol table
   **/
  public DivideExpression(SsaEnvironment e,SsaSymTab symtab){
    env=e;
    sstab=symtab;
    env.println("  Divide Expressions into 3 Address Expression",
                SsaEnvironment.MsgThr);
  }

  /**
   * Divide the expressions into 3 address expression.
   * @param f The current function
   * @param args The list of options
   **/
  public boolean doIt(Function f,ImList args){
    env.println("****************** doing DIVEX to "+f.symbol.name,
                SsaEnvironment.MinThr);

    for(BiLink p=f.flowGraph().basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        q.setElem(divide(node,q,false,false));
      }
    }

    env.println("",THR);

    f.touch();
    return(true);
  }

  
  LirNode divDefUseNode(LirNode node, BiLink link){
	  LirNode newNode = null;
	  Symbol dstSym=sstab.newSsaSymbol(DIVEX,node.type);
      // null if the type is aggregate
      if(dstSym!=null){
        LirNode nn=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);
        newNode=env.lir.operator(Op.SET,node.type,nn,node.kid(1),ImList.Empty);
        link.addBefore(newNode);
      }
      return newNode;
  }
  
  
  boolean defUseNode(LirNode node){
      if(node.opCode!=Op.SET || node.kid(0).opCode!=Op.REG)return false;
      if(node.kid(1).nKids()==0){
    	  return node.kid(1).equals(node.kid(0));
      }else if(node.kid(1).nKids()==1){
    	  return (node.kid(1).kid(0).equals(node.kid(0)));
      }else if(node.kid(1).nKids()==2){
    	  return (node.kid(1).kid(0).equals(node.kid(0)) || node.kid(1).kid(1).equals(node.kid(0)));
      }

      return false;
  }
  
  
  /**
   * Divide the expression into 3 address expression recursively.
   * @param node The current LIR node
   * @param link The place where the new expression attachs to
   * @param setSrc Whether the current LIR node is from the source operands
   *               of the SET operator
   * @param setDst Whether the current LIR node is from the destination
   *               operands of the SET operator
   * @return The divided LIR node
   **/
  LirNode divide(LirNode node,BiLink link,boolean setSrc,boolean setDst){
    LirNode result;

    switch(node.opCode){
      // memory operator
      case Op.MEM:{
        LirNode leftNode=divide(node.kid(0),link,false,false);

        LirNode oper=env.lir.operator(node.opCode,node.type,leftNode,
                                      node.opt);
        if(setDst){
          result=oper;
        }
        else{
          Symbol dstSym=sstab.newSsaSymbol(DIVEX,node.type);
          // null if the type is aggregate
          if(dstSym!=null){
            result=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);

            LirNode dst=env.lir.operator(Op.SET,node.type,result,oper,
                                         node.opt);
            link.addBefore(dst);
          }
          else
            result=oper;
        }


        break;
      }
      // unary operators
      case Op.NEG:
      case Op.BNOT:
      // cast operators
      case Op.CONVSX:
      case Op.CONVZX:
      case Op.CONVIT:
      case Op.CONVFX:
      case Op.CONVFT:
      case Op.CONVFI:
      case Op.CONVFS:
      case Op.CONVFU:
      case Op.CONVSF:
      case Op.CONVUF:{
        LirNode leftNode=divide(node.kid(0),link,false,false);

        LirNode oper=env.lir.operator(node.opCode,node.type,leftNode,
                                      node.opt);
        result=oper;

        if(setSrc){
          result=oper;
        }
        else{
          Symbol dstSym=sstab.newSsaSymbol(DIVEX,node.type);
          // null if the type is aggregate
          if(dstSym!=null){
            result=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);

            LirNode dst=env.lir.operator(Op.SET,node.type,result,oper,
                                         node.opt);
            link.addBefore(dst);
          }
          else
            result=oper;
          //env.output.println(dst);
        }
        break;
      }
      // binary operators
      case Op.BAND:
      case Op.BOR:
      case Op.BXOR:
      case Op.LSHS:
      case Op.LSHU:
      case Op.RSHS:
      case Op.RSHU:
      case Op.SUB:
      case Op.DIVS:
      case Op.DIVU:
      case Op.MODS:
      case Op.MODU:
      case Op.MUL:
      case Op.ADD:{
        LirNode leftNode=divide(node.kid(0),link,false,false);
        LirNode rightNode=divide(node.kid(1),link,false,false);

        LirNode oper=env.lir.operator(node.opCode,node.type,leftNode,
                                      rightNode,node.opt);
        if(setSrc){
          result=oper;
        }
        else{
          Symbol dstSym=sstab.newSsaSymbol(DIVEX,node.type);
          // null if the type is aggregate
          if(dstSym!=null){
            result=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);

            LirNode dst=env.lir.operator(Op.SET,node.type,result,oper,
                                         node.opt);
            link.addBefore(dst);
          }
          else
            result=oper;
          //env.output.println(dst);
        }

        break;
      }
      // The condition operator
      case Op.TSTEQ:
      case Op.TSTNE:
      case Op.TSTLTS:
      case Op.TSTLES:
      case Op.TSTGTS:
      case Op.TSTGES:
      case Op.TSTLTU:
      case Op.TSTLEU:
      case Op.TSTGTU:
      case Op.TSTGEU:{
        result=node.makeCopy(env.lir);

        // left side operand
        result.setKid(0,divide(result.kid(0),link,false,false));
        // right side operand
        result.setKid(1,divide(result.kid(1),link,false,false));

        break;
      }
      case Op.SET:{
    	  
    	  result=node.makeCopy(env.lir);
		  // source
		  LirNode n=divide(result.kid(1),link,true,false);
		  if(result.kid(0).opCode==Op.MEM && n.opCode!=Op.REG){
			  Symbol dstSym=sstab.newSsaSymbol(DIVEX,n.type);
			  // null if the type is aggregate
			  if(dstSym!=null){
				  LirNode nn=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);
				  LirNode newNode=env.lir.operator(Op.SET,n.type,nn,n,ImList.Empty);
				  link.addBefore(newNode);
				  n=nn.makeCopy(env.lir);
			  }
		  }
		  result.setKid(1,n);
		  // destination
		  result.setKid(0,divide(result.kid(0),link,false,true));  
    	  
    	  if(defUseNode(result)){
    		  result.setKid(1,(divDefUseNode(result,link)).kid(0));
    	  }
    	  
    	  break;
      }
      case Op.CALL:{
        result=node.makeCopy(env.lir);
        // 1st operand
        result.setKid(0,divide(result.kid(0),link,false,false));
        // 2nd operand
        result.setKid(1,divide(result.kid(1),link,false,false));
        // 3ed operand
        result.setKid(2,divide(result.kid(2),link,false,true));

        break;
      }
      case Op.JUMPC:{
        // 1st operand
        result=node.makeCopy(env.lir);
        result.setKid(0,divide(result.kid(0),link,false,false));

        break;
      }
      case Op.JUMPN:{
        // 1st operand
        result=node.makeCopy(env.lir);
        result.setKid(0,divide(result.kid(0),link,false,false));

        break;
      }
      case Op.LIST:{
        result=node.makeCopy(env.lir);
        for(int i=0;i<result.nKids();i++){
          //result.setKid(i,divide(result.kid(i),link,false,false));
          result.setKid(i,divide(result.kid(i),link,setSrc,setDst));
        }

        break;
      }
      case Op.FRAME:
      case Op.STATIC:{
        if(env.opt.isSet("ssa-extend-divex")){
          Symbol dstSym=sstab.newSsaSymbol(DIVEX,node.type);
          result=env.lir.symRef(Op.REG,dstSym.type,dstSym,ImList.Empty);
          LirNode dst=env.lir.operator(Op.SET,node.type,result,
                                       node.makeCopy(env.lir),node.opt);
          link.addBefore(dst);
          
          break;
        }
      }
      // nothing to do for LIR below
      case Op.PROLOGUE:
      case Op.EPILOGUE:
      case Op.PHI:
      case Op.JUMP:
      // Leaf
      case Op.REG:
      case Op.INTCONST:
      case Op.FLOATCONST:
      default:{
        result=node.makeCopy(env.lir);
      }
    }
    //env.output.println("##### "+result);
    return(result.makeCopy(env.lir));
  }
}
