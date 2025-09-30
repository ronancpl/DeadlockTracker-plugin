package deadlocktracker.graph.maker;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;

import deadlocktracker.DeadlockGraphMaker;
import deadlocktracker.containers.DeadlockClass;
import deadlocktracker.containers.DeadlockFunction;
import deadlocktracker.containers.DeadlockStorage;
import deadlocktracker.containers.Pair;
import deadlocktracker.graph.DeadlockAbstractType;
import deadlocktracker.graph.DeadlockGraphMethod;
import language.csharp.CSharpLexer;
import language.csharp.CSharpParser;

/**
 *
 * @author RonanLana
 */
public class CSharpGraph extends DeadlockGraphMaker {
	
	@Override
	public Integer getLiteralType(ParserRuleContext ctx) {
		CSharpParser.LiteralContext elemCtx = (CSharpParser.LiteralContext) ctx;
		
        if(elemCtx.INTEGER_LITERAL() != null || elemCtx.HEX_INTEGER_LITERAL() != null) return ElementalTypes[0];
        if(elemCtx.REAL_LITERAL() != null) return ElementalTypes[1];
        if(elemCtx.CHARACTER_LITERAL() != null) return ElementalTypes[2];
        //if(elemCtx.STRING() != null) return ElementalTypes[3];
        if(elemCtx.BIN_INTEGER_LITERAL() != null) return ElementalTypes[4];
        if(elemCtx.NULL_() != null) return ElementalTypes[7];
        
        return -1;
    }
	
	@Override
	public List<ParserRuleContext> getArgumentList(ParserRuleContext ctx) {
		CSharpParser.Argument_listContext expList = (CSharpParser.Argument_listContext) ctx;
		
        List<ParserRuleContext> ret = new LinkedList<>();
        if(expList != null) {
            for(CSharpParser.ArgumentContext exp : expList.argument()) {
            	ret.add(exp.expression());
            }
        }
        
        return ret;
	}
	
    private Integer getPrimitiveType(ParserRuleContext ctx) {
		CSharpParser.Simple_typeContext elemCtx = (CSharpParser.Simple_typeContext) ctx;
		
		if (elemCtx.numeric_type() != null) {
			CSharpParser.Numeric_typeContext numCtx = elemCtx.numeric_type();
			
			if (numCtx.integral_type() != null && numCtx.integral_type().CHAR() != null) return ElementalTypes[2];
			else if (numCtx.integral_type() != null || numCtx.DECIMAL() != null) return ElementalTypes[0];
			else if (numCtx.floating_point_type() != null) return ElementalTypes[1];
			else if(elemCtx.BOOL() != null) return ElementalTypes[4];
		}
        
        return -2;
    }
    
	@Override
	public Set<Integer> getMethodReturnType(DeadlockGraphMethod node, Integer classType, ParserRuleContext expCtx, DeadlockFunction sourceMethod, DeadlockClass sourceClass) {
        Set<Integer> retTypes = new HashSet<>();
        
        if(classType == -2) {
            retTypes.add(-2);
            return retTypes;
        }
        
        CSharpParser.Primary_expressionContext exp = (CSharpParser.Primary_expressionContext) expCtx;
        if (exp.method_invocation() != null) {
        	//System.out.println("CALL METHODRETURNTYPE for " + classType + " methodcall " + exp.getText());
            List<Integer> argTypes = getArgumentTypes(node, exp.method_invocation(0).argument_list(), sourceMethod, sourceClass);
            String methodName = exp.primary_expression_start().getText();
            
            if(!ReflectedClasses.containsKey(classType)) {
                DeadlockAbstractType absType = AbstractDataTypes.get(classType);
                if(absType != null) {
                    Integer ret = evaluateAbstractFunction(node, methodName, argTypes, classType, absType);
                    retTypes.add(ret);
                    
                    //if(ret == -1 && absType != DeadlockAbstractType.LOCK) System.out.println("SOMETHING OUT OF CALL FOR " + exp.IDENTIFIER().getText() + " ON " + absType /*+ dataNames.get(expType)*/);
                    return retTypes;
                } else {
                    retTypes = getReturnType(node, methodName, classType, argTypes, exp);
                    if(retTypes.contains(-1)) {
                        retTypes.remove(-1);
                        retTypes.add(getPreparedReturnType(methodName, classType)); // test for common function names widely used, regardless of data type
                    }

                    return retTypes;
                }
            } else {
                // follows the return-type pattern for the reflected classes, that returns an specific type if a method name has been recognized, returns the default otherwise
                Pair<Integer, Map<String, Integer>> reflectedData = ReflectedClasses.get(classType);
                
                if(methodName.contentEquals("toString")) {
                    retTypes.add(ElementalTypes[3]);
                } else {
                    DeadlockAbstractType absType = AbstractDataTypes.get(classType);
                    if(absType != null) {
                        if (absType == DeadlockAbstractType.LOCK || absType == DeadlockAbstractType.SCRIPT) {
                            Integer ret = evaluateAbstractFunction(node, methodName, argTypes, classType, absType);
                            retTypes.add(ret);

                            //if(ret == -1 && absType != DeadlockAbstractType.LOCK) System.out.println("SOMETHING OUT OF CALL FOR " + exp.IDENTIFIER().getText() + " ON " + absType /*+ dataNames.get(expType)*/);
                            return retTypes;
                        }
                    }
                    
                    Integer ret = reflectedData.right.get(methodName);
                    if(ret == null) ret = reflectedData.left;
                    retTypes.add(ret);
                }
            }
        }
        
        return retTypes;
    }
	
	private static CSharpParser.Unary_expressionContext generateDereferencedContext(String typeName) {
        String str = typeName;
        CSharpLexer lexer = new CSharpLexer(CharStreams.fromString(str));
        CommonTokenStream commonTokenStream = new CommonTokenStream(lexer);
        CSharpParser parser = new CSharpParser(commonTokenStream);
        
        return parser.unary_expression();
    }
	
	@Override
	public Set<Integer> parseMethodCalls(DeadlockGraphMethod node, ParserRuleContext exprCtx, DeadlockFunction sourceMethod, DeadlockClass sourceClass, boolean filter) {
		Set<Integer> ret = new HashSet<>();
		
		if (exprCtx instanceof CSharpParser.Unary_expressionContext) {
			CSharpParser.Unary_expressionContext expr = (CSharpParser.Unary_expressionContext) exprCtx;
			
			CSharpParser.Primary_expressionContext curCtx = expr.primary_expression();
	        if (curCtx != null) {
	        	CSharpParser.Primary_expression_startContext priCtx = curCtx.primary_expression_start();
                
                if(priCtx instanceof CSharpParser.LiteralExpressionContext) {
                    ret.add(getLiteralType(priCtx));
                    return ret;
                } else if(priCtx instanceof CSharpParser.ThisReferenceExpressionContext) {
                    ret.add(getThisType(sourceClass));
                    return ret;
                } else if(priCtx instanceof CSharpParser.ObjectCreationExpressionContext) {
	                CSharpParser.ObjectCreationExpressionContext cresCtx = (CSharpParser.ObjectCreationExpressionContext) priCtx;
	                
	                CSharpParser.Type_Context nameCtx = cresCtx.type_();
	                String idName = nameCtx.base_type().getText();
	                
	                if(curCtx.getChild(curCtx.getChildCount() - 1).getText().contentEquals("*")) {
	                	String outerName = nameCtx.getText();
	                	if (outerName.endsWith("*")) outerName = outerName.substring(0, outerName.lastIndexOf("*"));
	                	
	                	for (Integer typeId : parseMethodCalls(node, generateDereferencedContext(outerName), sourceMethod, sourceClass)) {
	                		if (typeId > -1) {
	                			DeadlockClass outerClass = ClassDataTypes.get(typeId);
			                	
		                        Integer derType;
		                        if (outerName.endsWith("*")) {
		                            derType = getDereferencedType(outerName, outerClass);
		                        } else {
		                            DeadlockClass mdc = DeadlockStorage.locateClass(outerName, sourceClass);
		                            if (mdc != null) {
		                                derType = ClassDataTypeIds.get(mdc);
		                            } else if (BasicDataTypeIds.containsKey(outerName)) {
		                                derType = BasicDataTypeIds.get(outerName);
		                            } else {
		                                derType = -2;
		                            }
		                        }
		                        
		                        ret.add(derType);
			                    
			                    return ret;
	                		}
	                	}
	                }
	                
                    DeadlockClass c = DeadlockStorage.locateClass(idName, sourceClass);
                    
                    if(c != null && c.getMaskedTypeSet() == null) {     // if the creator is instancing a compound data type, let it throw a -2
                        ret.add(ClassDataTypeIds.get(c));
                        return ret;
                    } else {
                    	ret.add(getPrimitiveType(nameCtx.base_type().simple_type()));
	                    return ret;
                    }
	            } else {
	                if (curCtx.primary_expression_start() instanceof CSharpParser.MemberAccessExpressionContext) {
	                	CSharpParser.MemberAccessExpressionContext maeCtx = ((CSharpParser.MemberAccessExpressionContext) curCtx.primary_expression_start());
	                    CSharpParser.IdentifierContext expCtx;
	                    if (maeCtx.qualified_alias_member() != null) {
	                    	expCtx = maeCtx.qualified_alias_member().identifier(0);
	                    	
	                    	if (!curCtx.primary_expression_start().getText().contentEquals("this")) {
                    			for (int i = 0; i < curCtx.getChildCount(); i++) {
                    				ParserRuleContext chCtx = (ParserRuleContext) curCtx.getChild(i);
                    		
			                    	Set<Integer> metRetTypes = parseMethodCalls(node, chCtx, sourceMethod, sourceClass);
			                        if (metRetTypes.size() > 0) {
			                            for (Integer expType : metRetTypes) {
			                                if(expType == null) System.out.println("null on " + expCtx.getText() + " src is " + DeadlockStorage.getCanonClassName(sourceClass));
		                                	if(expType != -1) {
		                                        if(expType != -2) {     // expType -2 means the former expression type has been excluded from the search
		                                            if(chCtx instanceof CSharpParser.Method_invocationContext) {
		                                                Set<Integer> r = getMethodReturnType(node, expType, curCtx, sourceMethod, sourceClass);
		                                                ret.addAll(r);
		                                                
		                                                if(ret.contains(-1)) {
		                                                    DeadlockClass c = getClassFromType(expType);
		                                                    if(c != null && c.isInterface()) {  // it's an interface, there's no method implementation to be found there
		                                                        ret.remove(-1);
		                                                        ret.add(-2);
		                                                    }
		                                                }
	
		                                                continue;
		                                            } else if(chCtx instanceof CSharpParser.IdentifierContext) {
		                                                if(isIgnoredType(expType)) {
		                                                    ret.add(-2);
		                                                    continue;
		                                                }
		                                                
		                                                CSharpParser.IdentifierContext idCtx = (CSharpParser.IdentifierContext) chCtx;
	
		                                                DeadlockClass c = getClassFromType(expType);
		                                                Set<Integer> templateTypes = null;
	
		                                                if(c == null) {
		                                                    List<Integer> cTypes = CompoundDataTypes.get(expType);
		                                                    if(cTypes != null) {
		                                                        c = getClassFromType(cTypes.get(cTypes.size() - 1));
	
		                                                        if(c == null) {
		                                                            //System.out.println("Compound FAILED @ " + cTypes.get(cTypes.size() - 1));
		                                                        } else {
		                                                            templateTypes = c.getMaskedTypeSet();
		                                                        }
		                                                    }
	
		                                                    if(c == null) {
		                                                        //String typeName = BasicDataTypes.get(expType);
	
		                                                        //System.out.println("FAILED @ " + expType);
		                                                        System.out.println("[Warning] No datatype found for " + idCtx + " on expression " + curCtx.getText() + " srcclass " + DeadlockStorage.getCanonClassName(sourceClass) + " detected exptype " + expType);
		                                                        ret.add(-2);
		                                                        continue;
		                                                    }
		                                                } else {
		                                                    if(c.isEnum()) {    // it's an identifier defining an specific item from an enum, return self-type
		                                                        if(idCtx.getText().contentEquals("length")) {
		                                                            ret.add(ElementalTypes[0]);
		                                                            continue;
		                                                        }
	
		                                                        ret.add(expType);
		                                                        continue;
		                                                    }
	
		                                                    templateTypes = c.getMaskedTypeSet();
		                                                }
		                                                
		                                                String element = idCtx.getText();
		                                                
		                                                Integer type = getPrimaryTypeOnFieldVars(element, c);
		                                                if(type == null) {
		                                                    DeadlockClass mdc = DeadlockStorage.locateInternalClass(element, c);  // element could be a private class reference
		                                                    if(mdc != null) {
		                                                        ret.add(ClassDataTypeIds.get(mdc));
		                                                        continue;
		                                                    }
	
		                                                    //System.out.println("SOMETHING OUT OF CALL FOR FIELD " + curCtx.IDENTIFIER().getText() + " ON " + DeadlockStorage.getCanonClassName(c));
		                                                    ret.add(-1);
		                                                    continue;
		                                                }
	
		                                                ret.add(getRelevantType(type, templateTypes, c, expType));
		                                                continue;
		                                            }
		                                        } else {
		                                            ret.add(-2);
		                                            continue;
		                                        }
		                                    } else {
			                                    ret.add(expType);
			                                    continue;
			                                }
		                                }
		                            }
                				}
		                            
	                            return ret;
	                        }
	                    }
	                }
    	    	}
	        } else {
	        	CSharpParser.Cast_expressionContext castCtx = expr.cast_expression();
	        	if (castCtx != null) {
	            	parseMethodCalls(node, castCtx.unary_expression(), sourceMethod, sourceClass);
	    	        String typeText = castCtx.type_().getText();
	    	        
	    	        DeadlockClass c = DeadlockStorage.locateClass(typeText, sourceClass);
	    	        if(c != null) {
	    	            ret.add(ClassDataTypeIds.get(c));
	    	            return ret;
	    	        }
	    	        
	    	        Integer i = BasicDataTypeIds.get(typeText);
	    	        ret.add((i != null) ? i : -2);
	    	        return ret;
	            }
	        }
		}
		
        ret.add(-1);
        return ret;
    }
	
	@Override
	public String parseMethodName(ParserRuleContext callCtx) {
		CSharpParser.Primary_expressionContext call = (CSharpParser.Primary_expressionContext) callCtx;
		
		String methodName = "";
        if (!call.method_invocation().isEmpty()) {
            methodName = ((CSharpParser.SimpleNameExpressionContext) call.primary_expression_start()).getText();
        } else if (!call.member_access().isEmpty()) {
        	methodName = ((CSharpParser.SimpleNameExpressionContext) call.primary_expression_start()).getText() + "." + call.member_access().get(0).getText();
        }
        
        return methodName;
	}
	
}
