package coins.ssa;

import coins.backend.LocalTransformer;
import coins.backend.Data;
import coins.backend.Function;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirSymRef;
import coins.backend.cfg.BasicBlk;
import coins.backend.util.BiLink;
import coins.backend.Op;
import coins.backend.util.ImList;

import java.io.*;

public class Papi implements LocalTransformer {

    public boolean doIt(Data data, ImList args) { return true; }
    public String name() { return "Papi"; }
    public String subject() {
	return "Papi";
    }

    public static final int THR=SsaEnvironment.OptThr;
    /** The threshold of debug print **/
    public static final int THR2=SsaEnvironment.AllThr;
    private SsaEnvironment env;
    private Function f;


    public Papi(SsaEnvironment e, SsaSymTab tab){
      env=e;
    }


    private LirNode makeCallStart() {
    	LirNode callNode = null;
    	try {
   	 		String callStr = "(CALL (STATIC I32 \"papi_start\") () ())";
   	 		ImList callSexp = (ImList)ImList.readSexp(new StringReader(callStr));
   	 		callNode = env.lir.decodeLir(callSexp, f, f.module);
    	} catch  (Exception e) {
    		System.err.println("Papi: transformation error!");
    		e.printStackTrace();
    		System.exit(1);
    	}
    	return callNode;
    }

    private LirNode makeCallEnd() {
    	LirNode callNode = null;
    	try {
    		String callStr = "(CALL (STATIC I32 \"papi_end\") () ())";
		    ImList callSexp = (ImList)ImList.readSexp(new StringReader(callStr));
		    callNode = env.lir.decodeLir(callSexp, f, f.module);
    	} catch  (Exception e) {
    		System.err.println("Papi: transformation error!");
    		e.printStackTrace();
    		System.exit(1);
    	} 
		return callNode;
    }

    
    public boolean doIt(Function function,ImList args) {

	f = function;

	LirNode edFunc = null;
	// Insert the counter variable
	if (f.symbol.name.intern() == "main".intern()) {
		
//		try {
//			String symLongStr = "(\"long_long\" STATIC I32 4 \".bss\" XDEF &syminfo \"long_long\" \""+f.module.name+"\" 2 0)";
//			ImList symLongSexp = (ImList)ImList.readSexp(new StringReader(symLongStr));
//			env.module.globalSymtab.addSymbol(symLongSexp);
//
//			String symValuesStr = "(\"values\" STATIC A320 4 \".bss\" XDEF &syminfo \"values\" \""+f.module.name+"\" 2 0)";
//			ImList symValuesSexp = (ImList)ImList.readSexp(new StringReader(symValuesStr));
//			env.module.globalSymtab.addSymbol(symValuesSexp);
//
//			String dataLongStr = "(DATA \"long_long\" (SPACE 4))";
//			ImList dataLongSexp = (ImList)ImList.readSexp(new StringReader(dataLongStr));
//			env.module.elements.add(new Data(f.module, dataLongSexp));
//
//			String dataValuesStr = "(DATA \"values\" (SPACE 40))";
//			ImList dataValuesSexp = (ImList)ImList.readSexp(new StringReader(dataValuesStr));
//			env.module.elements.add(new Data(f.module, dataValuesSexp));
//		} catch (Exception e) {
//			System.err.println("Global variables error!");
//			System.exit(1);
//		}
		
		LirNode stFunc = makeCallStart();
		edFunc = makeCallEnd();
	    f.flowGraph().entryBlk().instrList().first().addAfter(stFunc.makeCopy(env.lir));
	    f.flowGraph().exitBlk().instrList().last().addBefore(edFunc.makeCopy(env.lir));
	}

	for(BiLink pp=f.flowGraph().basicBlkList.first();!pp.atEnd();pp=pp.next()){

	    BasicBlk v=(BasicBlk)pp.elem();
	    if (v == f.flowGraph().exitBlk()) continue;

	    for(BiLink p=v.instrList().first();!p.atEnd();p=p.next()){
		LirNode node=(LirNode)p.elem();

		if(node.opCode==Op.CALL){
			if(node.kid(0).opCode==Op.STATIC){
				if(((LirSymRef)node.kid(0)).symbol.name.intern() == "exit".intern()){
					if(edFunc==null)edFunc = makeCallEnd();
				    p.addBefore(edFunc.makeCopy(env.lir));
				    continue;
				}
			}
//			if(node.kid(0).opCode==Op.MEM){
//				System.out.println("kid.kid:"+node.kid(0).kid(0));
//				if(((LirSymRef)node.kid(0).kid(0)).symbol.name.intern() == "exit".intern()){
//					if(edFunc==null)edFunc = makeCallEnd();
//				    p.addBefore(edFunc.makeCopy(env.lir));
//				    continue;
//				}
//			}
		}
	    }
	}

	f.flowGraph().touch();
	return true;
    }
}
