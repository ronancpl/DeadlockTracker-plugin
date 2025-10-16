/*
    This file is part of the DeadlockTracker detection tool
    Copyleft (L) 2025 RonanLana

    GNU General Public License v3.0

    Permissions of this strong copyleft license are conditioned on making available complete
    source code of licensed works and modifications, which include larger works using a licensed
    work, under the same license. Copyright and license notices must be preserved. Contributors
    provide an express grant of patent rights.
 */
package deadlocktracker.graph.maker;

import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import deadlocktracker.DeadlockGraphMaker;
import deadlocktracker.containers.DeadlockClass;
import deadlocktracker.containers.DeadlockFunction;
import deadlocktracker.containers.DeadlockStorage;
import deadlocktracker.containers.Pair;
import deadlocktracker.graph.DeadlockAbstractType;
import deadlocktracker.graph.DeadlockGraphMethod;
import deadlocktracker.source.CSharpReader;
import language.csharp.CSharpLexer;
import language.csharp.CSharpParser;

/**
 *
 * @author RonanLana
 */
public class CSharpGraph extends DeadlockGraphMaker {

	private static String methodName;
	private static Stack<Integer> expType = new Stack<>();

	@Override
	public void parseSourceFile(String fileName, ParseTreeListener listener) {
		try {
			((CSharpReader) listener).setPackageNameFromFilePath(fileName);

			CSharpLexer lexer = new CSharpLexer(CharStreams.fromFileName(fileName));
			CommonTokenStream commonTokenStream = new CommonTokenStream(lexer);
			CSharpParser parser = new CSharpParser(commonTokenStream);
			ParseTree tree = parser.compilation_unit();

			ParseTreeWalker walker = new ParseTreeWalker();
			walker.walk(listener, tree);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	@Override
	public Integer getLiteralType(ParserRuleContext ctx) {
		CSharpParser.LiteralContext elemCtx = ((CSharpParser.LiteralExpressionContext) ctx).literal();

		if(elemCtx.INTEGER_LITERAL() != null || elemCtx.HEX_INTEGER_LITERAL() != null) return ElementalTypes[0];
		if(elemCtx.REAL_LITERAL() != null) return ElementalTypes[1];
		if(elemCtx.CHARACTER_LITERAL() != null) return ElementalTypes[2];
		if(elemCtx.string_literal() != null) return ElementalTypes[3];
		if(elemCtx.BIN_INTEGER_LITERAL() != null || elemCtx.boolean_literal() != null) return ElementalTypes[4];
		if(elemCtx.NULL_() != null) return ElementalTypes[7];

		return -1;
	}

	private void fetchUnaryExpressionsFromContext(ParserRuleContext ctx, List<ParserRuleContext> list) {
		if (ctx instanceof CSharpParser.Unary_expressionContext) {
			list.add(ctx);
		} else {
			int size = list.size();
			for (int i = 0; i < ctx.getChildCount(); i++) {
				if (ctx.getChild(i) instanceof ParserRuleContext && list.size() == size) {
					ParserRuleContext child = (ParserRuleContext) ctx.getChild(i);
					fetchUnaryExpressionsFromContext(child, list);
				}
			}
		}
	}

	@Override
	public List<ParserRuleContext> getArgumentList(ParserRuleContext ctx) {
		CSharpParser.Argument_listContext expList = (CSharpParser.Argument_listContext) ctx;

		List<ParserRuleContext> ret = new LinkedList<>();
		if(expList != null) {
			for(CSharpParser.ArgumentContext exp : expList.argument()) {
				fetchUnaryExpressionsFromContext(exp.expression(), ret);
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

		if (expCtx != null) {
			if (expCtx instanceof CSharpParser.Method_invocationContext) {
				CSharpParser.Method_invocationContext exp = (CSharpParser.Method_invocationContext) expCtx;
				String methodName = this.methodName;

				List<Integer> argTypes = getArgumentTypes(node, exp.argument_list(), sourceMethod, sourceClass);

				if(!ReflectedClasses.containsKey(classType)) {
					DeadlockAbstractType absType = AbstractDataTypes.get(classType);
					if(absType != null) {
						Integer ret = evaluateAbstractFunction(node, methodName, argTypes, classType, absType);
						retTypes.add(ret);

						//if(ret == -1 && absType != DeadlockAbstractType.LOCK) System.out.println("SOMETHING OUT OF CALL FOR " + exp.IDENTIFIER().getText() + " ON " + absType /*+ dataNames.get(expType)*/);
						return retTypes;
					} else {
						retTypes = getReturnType(node, methodName, classType, argTypes, exp);

						//System.out.println("CALL METHODRETURNTYPE for " + classType + " methodcall " + methodName + " with " + exp.getText() + " result " + retTypes);
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
			} else if (expCtx instanceof CSharpParser.Member_accessContext) {
				CSharpParser.Member_accessContext exp = (CSharpParser.Member_accessContext) expCtx;

				Integer ret = getTypeFromIdentifier(classType, exp.identifier().IDENTIFIER().getText(), sourceMethod);
				retTypes.add(ret);
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

	private Integer getNameType(String name, DeadlockClass sourceClass) {
		DeadlockClass mdc = DeadlockStorage.locateClass(name, sourceClass);
		if (mdc != null) {
			return ClassDataTypeIds.get(mdc);
		} else if (BasicDataTypeIds.containsKey(name)) {
			return BasicDataTypeIds.get(name);
		} else {
			return -2;
		}
	}

	private Integer getCastType(DeadlockGraphMethod node, CSharpParser.Cast_expressionContext castCtx, DeadlockFunction sourceMethod, DeadlockClass sourceClass) {
		expType.push(0);
		parseMethodCalls(node, castCtx.unary_expression(), sourceMethod, sourceClass);
		expType.pop();

		String typeText = castCtx.type_().getText();

		DeadlockClass c = DeadlockStorage.locateClass(typeText, sourceClass);
		if(c != null) {
			return ClassDataTypeIds.get(c);
		}

		Integer i = BasicDataTypeIds.get(typeText);
		return ((i != null) ? i : -2);
	}

	@Override
	public Set<Integer> parseMethodCalls(DeadlockGraphMethod node, ParserRuleContext exprCtx, DeadlockFunction sourceMethod, DeadlockClass sourceClass, boolean filter) {
		if (filter) {
			refClass = sourceClass;
		}

		Set<Integer> ret = new HashSet<>();
		if (exprCtx instanceof CSharpParser.Unary_expressionContext) {
			CSharpParser.Unary_expressionContext expr = (CSharpParser.Unary_expressionContext) exprCtx;
			CSharpParser.Primary_expressionContext curCtx = expr.primary_expression();

			CSharpParser.Cast_expressionContext castCtx = expr.cast_expression();
			if (castCtx != null) {
				ret.add(getCastType(node, castCtx, sourceMethod, sourceClass));
				return ret;
			} else {
				if (curCtx != null) {
					if (!sourceClass.getName().contentEquals("_DefaultClass")) {
						this.expType.push(ClassDataTypeIds.get(sourceClass));
					} else {
						this.expType.push(-2);
					}

					int c = 0;
					for (int i = 0; i < curCtx.getChildCount(); i++) {
						if (curCtx.getChild(i) instanceof ParserRuleContext) {
							ParserRuleContext chCtx = (ParserRuleContext) curCtx.getChild(i);

							Set<Integer> metRetTypes = parseMethodCalls(node, chCtx, sourceMethod, sourceClass);
							if (metRetTypes.size() > 0) {
								for (Integer expType : metRetTypes) {
									if(expType == null) System.out.println("null on " + expr.getText() + " src is " + DeadlockStorage.getCanonClassName(sourceClass));
									if(expType != -1) {
										if (ClassDataTypes.get(expType) != null) refClass = ClassDataTypes.get(expType);

										this.expType.push(expType);
										c++;

										if(expType == -2) {     // expType -2 means the former expression type has been excluded from the search
											break;
										}
									} else {
										ret.add(expType);
										continue;
									}
								}
							}
						}
					}

					Integer type = expType.pop();
					ret.add(type);

					for (int b = 0; b < c; b++) expType.pop();

					return ret;
				} else {
					ret.addAll(parseMethodCalls(node, ((CSharpParser.Unary_expressionContext) exprCtx).unary_expression(), sourceMethod, sourceClass, false));
					return ret;
				}
			}
		} else if(exprCtx instanceof CSharpParser.Method_invocationContext) {
			Set<Integer> r = getMethodReturnType(node, expType.peek(), exprCtx, sourceMethod, sourceClass);
			ret.addAll(r);

			return ret;
		} else if(exprCtx instanceof CSharpParser.IdentifierContext) {
			if(isIgnoredType(expType.peek())) {
				ret.add(-2);
				return ret;
			}

			CSharpParser.IdentifierContext idCtx = (CSharpParser.IdentifierContext) exprCtx;

			DeadlockClass c = getClassFromType(expType.peek());
			Set<Integer> templateTypes = null;

			if(c == null) {
				List<Integer> cTypes = CompoundDataTypes.get(expType.peek());
				if(cTypes != null) {
					c = getClassFromType(cTypes.get(cTypes.size() - 1));

					if(c == null) {
						//System.out.println("Compound FAILED @ " + cTypes.get(cTypes.size() - 1));
					} else {
						templateTypes = c.getMaskedTypeSet();
					}
				}

				if(c == null) {
					//String typeName = EveryDataTypes.get(expType.peek());

					//System.out.println("FAILED @ " + expType);
					System.out.println("[Warning] No datatype found for " + idCtx + " on expression " + exprCtx.getText() + " srcclass " + DeadlockStorage.getCanonClassName(sourceClass) + " detected exptype " + expType.peek());
					ret.add(-2);
					return ret;
				}
			} else {
				if(c.isEnum()) {    // it's an identifier defining an specific item from an enum, return self-type
					if(idCtx.getText().contentEquals("length")) {
						ret.add(ElementalTypes[0]);
						return ret;
					}

					ret.add(expType.peek());
					return ret;
				}

				templateTypes = c.getMaskedTypeSet();
			}

			String element = idCtx.getText();

			Integer type = getPrimaryTypeOnFieldVars(element, c);
			if(type == null) {
				DeadlockClass mdc = DeadlockStorage.locateInternalClass(element, c);  // element could be a private class reference
				if(mdc != null) {
					ret.add(ClassDataTypeIds.get(mdc));
					return ret;
				}

				//System.out.println("SOMETHING OUT OF CALL FOR FIELD " + curCtx.IDENTIFIER().getText() + " ON " + DeadlockStorage.getCanonClassName(c));
				ret.add(-1);
				return ret;
			}

			ret.add(getRelevantType(type, templateTypes, c, expType.peek()));
			return ret;
		} else if(exprCtx instanceof CSharpParser.SimpleNameExpressionContext) {
			methodName = exprCtx.getText();

			Integer typeId = getTypeFromIdentifier(expType.peek(), exprCtx.getText(), sourceMethod);
			if (typeId == -1) typeId = expType.peek();
			ret.add(typeId);

			return ret;
		} else if(exprCtx instanceof CSharpParser.Member_accessContext) {
			CSharpParser.Member_accessContext maCtx = (CSharpParser.Member_accessContext) exprCtx;

			methodName = maCtx.identifier().getText();

			Integer typeId = getTypeFromIdentifier(expType.peek(), maCtx.identifier().getText(), sourceMethod);
			if (typeId == -1) typeId = expType.peek();
			ret.add(typeId);

			return ret;
		} else if(exprCtx instanceof CSharpParser.MemberAccessExpressionContext) {
			CSharpParser.MemberAccessExpressionContext maeCtx = ((CSharpParser.MemberAccessExpressionContext) exprCtx);
			if (maeCtx.qualified_alias_member() != null) {
				ret.add(getNameType(maeCtx.qualified_alias_member().getText(), sourceClass));
			} else {
				ret.add(getNameType(maeCtx.predefined_type().getText(), sourceClass));
			}

			return ret;
		} else if(exprCtx instanceof CSharpParser.LiteralExpressionContext) {
			ret.add(getLiteralType((CSharpParser.LiteralExpressionContext) exprCtx));
			return ret;
		} else if(exprCtx instanceof CSharpParser.ThisReferenceExpressionContext) {
			ret.add(getThisType(sourceClass));
			return ret;
		} else if(exprCtx instanceof CSharpParser.ObjectCreationExpressionContext) {
			CSharpParser.ObjectCreationExpressionContext cresCtx = (CSharpParser.ObjectCreationExpressionContext) exprCtx;

			CSharpParser.Type_Context nameCtx = cresCtx.type_();
			if (nameCtx != null) {
				String idName = nameCtx.base_type().getText();

				if(exprCtx.getChild(exprCtx.getChildCount() - 1).getText().contentEquals("*")) {
					String outerName = nameCtx.getText();
					if (outerName.endsWith("*")) outerName = outerName.substring(0, outerName.lastIndexOf("*"));
					expType.push(0);
					for (Integer typeId : parseMethodCalls(node, generateDereferencedContext(outerName), sourceMethod, sourceClass)) {
						if (typeId > -1) {
							DeadlockClass outerClass = ClassDataTypes.get(typeId);

							Integer derType;
							if (outerName.endsWith("*")) {
								derType = getDereferencedType(outerName, outerClass);
							} else {
								derType = getNameType(outerName, sourceClass);
							}
							ret.add(derType);
						}
					}
					expType.pop();
				}

				DeadlockClass c = DeadlockStorage.locateClass(idName, sourceClass);

				if(c != null && c.getMaskedTypeSet() == null) {     // if the creator is instancing a compound data type, let it throw a -2
					ret.add(ClassDataTypeIds.get(c));
				} else {
					CSharpParser.Base_typeContext baseCtx = nameCtx.base_type();
					if (baseCtx.simple_type() != null) {
						ret.add(getPrimitiveType(baseCtx.simple_type()));
					}
				}
			} else {
				ret.add(-2);
			}

			return ret;
		} else if(exprCtx instanceof CSharpParser.Bracket_expressionContext) {
			CSharpParser.Bracket_expressionContext brCtx = (CSharpParser.Bracket_expressionContext) exprCtx;

			for (CSharpParser.Indexer_argumentContext idxCtx : brCtx.indexer_argument()) {
				List<ParserRuleContext> list = new LinkedList<>();
				fetchUnaryExpressionsFromContext(idxCtx.expression(), list);

				for (ParserRuleContext ctx : list) {
					CSharpParser.Unary_expressionContext unaryCtx = (CSharpParser.Unary_expressionContext) ctx;
					for (Integer typeId : parseMethodCalls(node, unaryCtx, sourceMethod, sourceClass)) {
						ret.add(typeId);
					}
				}
			}

			return ret;
		} else if(exprCtx instanceof CSharpParser.ParenthesisExpressionsContext) {
			CSharpParser.ParenthesisExpressionsContext parCtx = (CSharpParser.ParenthesisExpressionsContext) exprCtx;
			List<ParserRuleContext> list = new LinkedList<>();
			fetchUnaryExpressionsFromContext(parCtx.expression(), list);

			for (ParserRuleContext ctx : list) {
				CSharpParser.Unary_expressionContext unaryCtx = (CSharpParser.Unary_expressionContext) ctx;
				for (Integer typeId : parseMethodCalls(node, unaryCtx, sourceMethod, sourceClass)) {
					ret.add(typeId);
				}
			}

			return ret;
		}

		ret.add(-1);
		return ret;
	}

	@Override
	public String parseMethodName(ParserRuleContext callCtx) {
		String methodName = "";

		if (callCtx instanceof CSharpParser.Unary_expressionContext) {
			CSharpParser.Primary_expressionContext call = ((CSharpParser.Unary_expressionContext) callCtx).primary_expression();
			if (call == null) {
				if (((CSharpParser.Unary_expressionContext) callCtx).cast_expression() != null) {
					return parseMethodName(((CSharpParser.Unary_expressionContext) callCtx).cast_expression().unary_expression());
				} else {
					return parseMethodName(((CSharpParser.Unary_expressionContext) callCtx).unary_expression());
				}
			}

			if (call.primary_expression_start() instanceof CSharpParser.SimpleNameExpressionContext) {
				if (call.method_invocation() != null) {
					methodName = ((CSharpParser.SimpleNameExpressionContext) call.primary_expression_start()).getText();
				} else if (call.member_access() != null) {
					methodName = ((CSharpParser.SimpleNameExpressionContext) call.primary_expression_start()).getText() + "." + call.member_access().get(0).getText();
				}
			}
		}

		return methodName;
	}

	@Override
	public ParserRuleContext generateExpression(String expressionText) {
		CSharpLexer lexer = new CSharpLexer(CharStreams.fromString(expressionText));
		CommonTokenStream commonTokenStream = new CommonTokenStream(lexer);
		CSharpParser parser = new CSharpParser(commonTokenStream);

		return parser.unary_expression();
	}

	@Override
	public boolean isUnlockMethodCall(String expressionText) {
		return expressionText.endsWith("unlock()");
	}

}
