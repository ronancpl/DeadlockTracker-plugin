/*
    This file is part of the DeadlockTracker detection tool
    Copyleft (L) 2025 RonanLana

    GNU General Public License v3.0

    Permissions of this strong copyleft license are conditioned on making available complete
    source code of licensed works and modifications, which include larger works using a licensed
    work, under the same license. Copyright and license notices must be preserved. Contributors
    provide an express grant of patent rights.
*/
package deadlocktracker.source;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

import deadlocktracker.containers.DeadlockClass;
import deadlocktracker.containers.DeadlockClass.DeadlockClassType;
import deadlocktracker.containers.DeadlockEnum;
import deadlocktracker.containers.DeadlockFunction;
import deadlocktracker.containers.DeadlockLock;
import deadlocktracker.containers.DeadlockStorage;
import deadlocktracker.containers.Pair;
import deadlocktracker.graph.DeadlockAbstractType;
import deadlocktracker.strings.IgnoredTypes;
import deadlocktracker.strings.LinkedTypes;
import deadlocktracker.strings.ReflectedTypes;
import language.csharp.CSharpLexer;
import language.csharp.CSharpParser;
import language.csharp.CSharpParserBaseListener;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

/**
 *
 * @author RonanLana
 */
public class CSharpReader extends CSharpParserBaseListener {
    private static DeadlockStorage storage = new DeadlockStorage();
    private static String syncLockTypeName = "SyncLock";
    
    // ---- cached storage fields ----
    private static Map<String, Map<String, DeadlockClass>> PublicClasses = storage.getPublicClasses();
    private static Map<String, Map<String, DeadlockClass>> PrivateClasses = storage.getPrivateClasses();
    
    private static Map<String, DeadlockLock> Locks = storage.getLocks();
    private static Map<String, DeadlockLock> ReadWriteLocks = storage.getReadWriteLocks();
    
    private static Map<DeadlockClass, Integer> ClassDataTypes = storage.getClassDataTypes();
    private static Map<List<Integer>, Integer> CompoundDataTypes = storage.getCompoundDataTypes();
    private static Map<String, Integer> BasicDataTypes = storage.getBasicDataTypes();
    private static Map<Integer, Integer> ElementalDataTypes = storage.getElementalDataTypes();
    private static Integer[] ElementalTypes = storage.getElementalTypes();
    
    private static Map<DeadlockClass, List<DeadlockClass>> InheritanceTree = storage.getInheritanceTree();
    private static Map<Integer, Pair<Integer, Map<String, Integer>>> ReflectedClasses = storage.getReflectedClasses();
    
    private static Map<DeadlockFunction, Boolean> RunnableFunctions = new HashMap<>();
    private static List<DeadlockFunction> RunnableMethods = storage.getRunnableMethods();
    
    //private static Map<Integer, String> CompoundDataNames = new HashMap();   // test purposes only
    
    // ---- volatile fields ----
    
    private static AtomicInteger runningId = new AtomicInteger(1);
    private static AtomicInteger runningSyncLockId = new AtomicInteger(0);
    private static AtomicInteger runningTypeId = new AtomicInteger(1);  // volatile id 0 reserved for sync locks
    private static AtomicInteger runningMethodCallCount = new AtomicInteger(0);
    
    private static Stack<Integer> methodCallCountStack = new Stack();
    private static Stack<DeadlockFunction> methodStack = new Stack();
    private static List<DeadlockClass> classStack = new ArrayList();
    private static Stack<Integer> syncLockStack = new Stack();
    
    private static Set<String> readLockWaitingSet = new HashSet();
    private static Set<String> writeLockWaitingSet = new HashSet();
    
    private static Map<String, String> readLockQueue = new HashMap();
    private static Map<String, String> writeLockQueue = new HashMap();
    
    private static Map<Integer, String> LinkedDataNames = new HashMap();
    
    private static List<String> currentImportList = new ArrayList<>();
    private static String sourceDirPrefixPath;
    private static Stack<String> currentPackageName = new Stack<>();
    private static String currentCompleteFileClassName;
    private static DeadlockClass currentClass = null;
    private static List<DeadlockClass> customClasses = new LinkedList<>();
    private static boolean currentAbstract = false;
    
    private static Map<Integer, Pair<DeadlockClass, Integer>> volatileMaskedTypes = new HashMap<>();
    private static Map<Integer, Pair<String, String>> volatileDataTypes = new HashMap<>();  // cannot recover the import classes at the first parsing, so the type definition comes at the second rundown
    
    public void setSourceDirPrefixPath(String sourceDirPath) {
        sourceDirPath = sourceDirPath.trim().toLowerCase();
        sourceDirPath = sourceDirPath.replace('\\', '/');
        
        int i = sourceDirPath.lastIndexOf('.') - 1;
        if (i < 0) i = sourceDirPath.length();
        
        while (i >= 0) {
            switch (sourceDirPath.charAt(i)) {
                case '.':
                    sourceDirPrefixPath = sourceDirPath.substring(sourceDirPath.indexOf("/", i) + 1) + "/";
                    i = -1;
                    break;
                    
                default:
            }
            
            i--;
        }
    }
    
    public void setPackageNameFromFilePath(String fileName) {
    	String str = new String(fileName);
    	str = str.replace('\\', '/');
    	
		int idx = str.lastIndexOf("/");
		if (idx > -1) {
			str = str.substring(0, idx + 1);			
		}
	
        idx = str.toLowerCase().indexOf(sourceDirPrefixPath);
        str = str.substring(idx + sourceDirPrefixPath.length());
        str = str.replace('/', '.');
        
        currentPackageName.push(str);
    }
    
    @Override
    public void enterCompilation_unit(CSharpParser.Compilation_unitContext ctx) {
        DeadlockFunction method = new DeadlockFunction("_global", null, null, currentAbstract);
        methodStack.add(method);
        
        currentImportList.clear();
    }
    
    @Override
    public void enterNamespace_declaration(CSharpParser.Namespace_declarationContext ctx) {
        currentPackageName.push(ctx.qualified_identifier().getText() + ".");
    }
    
    @Override
    public void exitNamespace_declaration(CSharpParser.Namespace_declarationContext ctx) {
        currentPackageName.pop();
    }
    
    @Override
    public void enterUsing_directives(CSharpParser.Using_directivesContext ctx) {
        for (CSharpParser.Using_directiveContext ctxd : ctx.using_directive()) {
            if (ctxd instanceof CSharpParser.UsingAliasDirectiveContext) {
                CSharpParser.UsingAliasDirectiveContext ctxa = (CSharpParser.UsingAliasDirectiveContext) ctxd;
        	
    		String s = ctxa.namespace_or_type_name().getText();
                currentImportList.add(s);
            }
    	}
    }
    
    @Override
    public void enterClass_member_declaration(CSharpParser.Class_member_declarationContext ctx) {
		currentAbstract = false;
        
		if (ctx.all_member_modifiers() != null) {
			for (CSharpParser.All_member_modifierContext ctxi : ctx.all_member_modifiers().all_member_modifier()) {
                currentAbstract |= (ctxi.ABSTRACT() != null);
			}
		}
    }
    
    @Override
    public void enterType_declaration(CSharpParser.Type_declarationContext ctx) {
        currentAbstract = false;
        
        if(ctx.attributes() != null) {
        	for (CSharpParser.Attribute_sectionContext ctxa : ctx.attributes().attribute_section()) {
        		if (ctxa.attribute_target() != null && ctxa.attribute_target().keyword() != null) {
    				currentAbstract |= (ctxa.attribute_target().keyword().ABSTRACT() != null);
        		}
        	}
        }
    }
    
    @Override
    public void enterType_argument_list(CSharpParser.Type_argument_listContext ctx) {
    	for(CSharpParser.Type_Context typC : ctx.type_()) {
            Integer mType = getTypeId(typC.getText(), currentCompleteFileClassName);
            
            volatileMaskedTypes.put(mType, new Pair<>(currentClass, currentClass.getMaskedTypeSize()));
            currentClass.addMaskedType(mType);
        }
    }
    
    private static List<String> getExtendedImplementedList(CSharpParser.Class_baseContext ttcCtx) {
        List<String> list = new LinkedList<>();
        
        if (ttcCtx != null) {
        	list.add(ttcCtx.class_type().namespace_or_type_name().getText());
            for(CSharpParser.Namespace_or_type_nameContext tt : ttcCtx.namespace_or_type_name()) {
                list.add(tt.getText());
            }	
        }
        
        return list;
    }
    
    private static List<String> getExtendedImplementedListForEnum(CSharpParser.Enum_baseContext ttcCtx) {
        List<String> list = new LinkedList<>();
        
        if (ttcCtx != null) {
        	list.add(ttcCtx.type_().getText());
        }
        
        return list;
    }
    
    private static List<String> getExtendedImplementedListForInterface(CSharpParser.Interface_baseContext ttcCtx) {
        List<String> list = new LinkedList<>();
        
        if (ttcCtx != null) {
        	for(CSharpParser.Namespace_or_type_nameContext tt : ttcCtx.interface_type_list().namespace_or_type_name()) {
                list.add(tt.getText());
            }	
        }
        
        return list;
    }
    
    private static String getPathName(String className) {
        String path = "";
        
        for(DeadlockClass mdc : classStack) {
            path += mdc.getName() + ".";
        }
        path += className;
        
        return path;
    }
    
    @Override
    public void enterClass_definition(CSharpParser.Class_definitionContext ctx) {
        String className = ctx.identifier().IDENTIFIER().getText();
        boolean isAbstract = currentAbstract;
        
        List<String> superNames = getExtendedImplementedList(ctx.class_base());
        
        if(currentClass != null) {
            classStack.add(currentClass);
            currentClass = new DeadlockClass(DeadlockClassType.CLASS, className, currentPackageName.peek(), getPathName(className), superNames, isAbstract, currentClass);
        } else {
            currentCompleteFileClassName = currentPackageName.peek() + className;
            
            int idx = className.indexOf(".");
            if (idx > -1) className = className.substring(idx + 1);
            
            currentClass = new DeadlockClass(DeadlockClassType.CLASS, className, currentPackageName.peek(), getPathName(className), superNames, isAbstract, null);
        }
        
        InheritanceTree.put(currentClass, new LinkedList<>());
    }
    
    @Override
    public void exitClass_definition(CSharpParser.Class_definitionContext ctx) {
        if(classStack.isEmpty()) {
            for(String s : currentImportList) {
                currentClass.addImport(s);
            }
            
            if(PublicClasses.containsKey(currentPackageName.peek())) {
                PublicClasses.get(currentPackageName.peek()).put(currentClass.getPathName(), currentClass);
            } else {
                PublicClasses.put(currentPackageName.peek(), newPackageClass(currentClass.getPathName(), currentClass));
            }
            
            currentClass = null;
        } else {
            String fcn = currentCompleteFileClassName;
            
            if(PrivateClasses.containsKey(fcn)) {
                PrivateClasses.get(fcn).put(getPathName(currentClass.getName()), currentClass);
            } else {
                PrivateClasses.put(fcn, newPackageClass(getPathName(currentClass.getName()), currentClass));
            }
            
            DeadlockClass mdc = currentClass;
            currentClass = classStack.remove(classStack.size() - 1);
            currentClass.addPrivateClass(mdc.getName(), mdc);
        }
    }
    
    @Override
    public void enterEnum_definition(CSharpParser.Enum_definitionContext ctx) {
        String className = ctx.identifier().IDENTIFIER().getText();
        
        List<String> superNames = getExtendedImplementedListForEnum(ctx.enum_base());
        
        if(currentClass != null) {
            classStack.add(currentClass);
            currentClass = new DeadlockEnum(className, currentPackageName.peek(), getPathName(className), superNames, currentClass);
        } else {
            currentCompleteFileClassName = currentPackageName.peek() + className;
            
            int idx = className.indexOf(".");
            if (idx > -1) className = className.substring(idx + 1);
            
            currentClass = new DeadlockEnum(className, currentPackageName.peek(), getPathName(className), superNames, null);
        }
        
        InheritanceTree.put(currentClass, new LinkedList<>());
    }
    
    @Override
    public void exitEnum_definition(CSharpParser.Enum_definitionContext ctx) {
        if(classStack.isEmpty()) {
            for(String s : currentImportList) {
                currentClass.addImport(s);
            }
            
            if(PublicClasses.containsKey(currentPackageName.peek())) {
                PublicClasses.get(currentPackageName.peek()).put(currentClass.getPathName(), currentClass);
            } else {
                PublicClasses.put(currentPackageName.peek(), newPackageClass(currentClass.getPathName(), currentClass));
            }
            
            currentClass = null;
        } else {
            String fcn = currentCompleteFileClassName;
            
            if(PrivateClasses.containsKey(fcn)) {
                PrivateClasses.get(fcn).put(getPathName(currentClass.getName()), currentClass);
            } else {
                PrivateClasses.put(fcn, newPackageClass(getPathName(currentClass.getName()), currentClass));
            }
            
            DeadlockClass mdc = currentClass;
            currentClass = classStack.remove(classStack.size() - 1);
            currentClass.addPrivateClass(mdc.getName(), mdc);
        }
    }
    
    @Override
    public void enterInterface_definition(CSharpParser.Interface_definitionContext ctx) {
        String className = ctx.identifier().IDENTIFIER().getText();
        
        List<String> superNames = getExtendedImplementedListForInterface(ctx.interface_base());
        
        if(currentClass != null) {
            classStack.add(currentClass);
            currentClass = new DeadlockClass(DeadlockClassType.INTERFACE, className, currentPackageName.peek(), getPathName(className), superNames, true, currentClass);
        } else {
            currentCompleteFileClassName = currentPackageName.peek() + className;
            currentClass = new DeadlockClass(DeadlockClassType.INTERFACE, className, currentPackageName.peek(), getPathName(className), superNames, true, null);
        }
        
        InheritanceTree.put(currentClass, new LinkedList<>());
    }
    
    @Override
    public void exitInterface_definition(CSharpParser.Interface_definitionContext ctx) {
        if(classStack.isEmpty()) {
            for(String s : currentImportList) {
                currentClass.addImport(s);
            }
            
            if(PublicClasses.containsKey(currentPackageName.peek())) {
                PublicClasses.get(currentPackageName.peek()).put(currentClass.getPathName(), currentClass);
            } else {
                PublicClasses.put(currentPackageName.peek(), newPackageClass(currentClass.getPathName(), currentClass));
            }
            
            currentClass = null;
        } else {
            String fcn = currentCompleteFileClassName;
            
            if(PrivateClasses.containsKey(fcn)) {
                PrivateClasses.get(fcn).put(currentClass.getPathName(), currentClass);
            } else {
                PrivateClasses.put(fcn, newPackageClass(currentClass.getPathName(), currentClass));
            }
            
            DeadlockClass mdc = currentClass;
            currentClass = classStack.remove(classStack.size() - 1);
            currentClass.addPrivateClass(mdc.getName(), mdc);
        }
    }
    
    @Override
    public void enterInterface_member_declaration(CSharpParser.Interface_member_declarationContext ctx) {
        CSharpParser.IdentifierContext idCtx = ctx.identifier();
        
        if(idCtx != null) {
            String curText = ctx.type_().getText();
            Integer type = getTypeId(curText, currentCompleteFileClassName);
            
            currentClass.addFieldVariable(type, idCtx.getText());
        }
    }
    
    private static Map<String, DeadlockClass> newPackageClass(String s, DeadlockClass c) {
        Map<String, DeadlockClass> m = new HashMap<>();
        m.put(s, c);
        
        return m;
    }
    
    private List<String> fullClassMethodName(List<String> list) {
    	List<String> ret = new ArrayList<>(2);
    	
    	String path = "";
    	String methodName = list.remove(list.size() - 1);
    	
    	for (String name : list) {
    		path += name + ".";
    	}
    	if (!path.isEmpty()) path = path.substring(0, path.length() - 1);
    	
    	ret.add(path);
    	ret.add(methodName);
    	
    	return ret;
    }
    
    private void enterMethodDeclaration(List<String> list, CSharpParser.Method_declarationContext ctx) {
    	String className = list.get(0);
    	String methodName = list.get(1);
    	
    	DeadlockClass mdc;
        if (!className.isEmpty()) {
            mdc = DeadlockStorage.locateClass(className, currentClass);
        } else {
            mdc = currentClass;
        }
        
        DeadlockFunction method = new DeadlockFunction(methodName, mdc, methodStack.isEmpty() ? null : methodStack.peek(), currentAbstract);
        Pair<Integer, Pair<List<Integer>, Map<Long, Integer>>> retParamTypes = getMethodMetadata(ctx, method);
        
        method.setMethodMetadata(retParamTypes.left, retParamTypes.right.left, retParamTypes.right.right);
        methodStack.add(method);
        
        methodCallCountStack.add(runningMethodCallCount.get());
        runningMethodCallCount.set(0);
    }
    
    private void exitMethodDeclaration() {
    	DeadlockFunction method = methodStack.pop();
        DeadlockClass mdc = method.getSourceClass();
        
        String methodName = method.getName();
        if(methodName.contentEquals("run") && method.getParameters().isEmpty()) {
            // book-keeping possible Runnable functions to be dealt with later on the parsing
            
            RunnableFunctions.put(method, !methodStack.isEmpty());
        }
        
        runningMethodCallCount.set(methodCallCountStack.pop());
    }
    
    @Override
    public void enterMethod_declaration(CSharpParser.Method_declarationContext ctx) {
    	List<String> list = new ArrayList<>();
    	for (CSharpParser.IdentifierContext name : ctx.method_member_name().identifier()) {
    		list.add(name.getText());
    	}
    	
    	enterMethodDeclaration(fullClassMethodName(list), ctx);
    }
    
    @Override
    public void exitMethod_declaration(CSharpParser.Method_declarationContext ctx) {
    	exitMethodDeclaration();
    }
    
    private void enterLocalFunctionDeclaration(List<String> list, CSharpParser.Local_function_declarationContext ctx) {
    	String className = list.get(0);
    	String methodName = list.get(1);
    	
    	DeadlockClass mdc = DeadlockStorage.locateClass(className, currentClass);
        
        DeadlockFunction method = new DeadlockFunction(methodName, mdc, methodStack.isEmpty() ? null : methodStack.peek(), currentAbstract);
        Pair<Integer, Pair<List<Integer>, Map<Long, Integer>>> retParamTypes = getLocalFunctionMetadata(ctx, method);
        
        method.setMethodMetadata(retParamTypes.left, retParamTypes.right.left, retParamTypes.right.right);
        methodStack.add(method);
        
        methodCallCountStack.add(runningMethodCallCount.get());
        runningMethodCallCount.set(0);
    }
    
    @Override
    public void enterLocal_function_declaration(CSharpParser.Local_function_declarationContext ctx) {
    	List<String> list = new ArrayList<>(2);
    	list.add("_");
    	list.add(ctx.local_function_header().identifier().IDENTIFIER().getText());
    	
    	enterLocalFunctionDeclaration(list, ctx);
    }
    
    @Override
    public void exitLocal_function_declaration(CSharpParser.Local_function_declarationContext ctx) {
    	exitMethodDeclaration();
    }
    
    @Override
    public void enterConstructor_declaration(CSharpParser.Constructor_declarationContext ctx) {
        String methodName = ctx.identifier().IDENTIFIER().getText();
        
        DeadlockFunction method = new DeadlockFunction(methodName, currentClass, null, false);
        Pair<List<Integer>, Map<Long, Integer>> pTypes = getMethodParameterTypes(ctx.formal_parameter_list(), method);
        
        method.setMethodMetadata(-1, pTypes.left, pTypes.right);
        methodStack.add(method);
    }
    
    @Override
    public void exitConstructor_declaration(CSharpParser.Constructor_declarationContext ctx) {
        DeadlockFunction method = methodStack.pop();
        if (currentClass != null) currentClass.addClassMethod(method);
    }
    
    @Override
    public void enterField_declaration(CSharpParser.Field_declarationContext ctx) {
    	List<String> vdNames = ctx.variable_declarators().variable_declarator().stream()
        .map(vdItem -> vdItem.identifier().getText())
        .collect(Collectors.toList());
    	
        processVariableDeclarations(true, ((CSharpParser.Typed_member_declarationContext) ctx.getParent()).type_().getText(), vdNames);
    }
    
    @Override
    public void enterEvent_declaration(CSharpParser.Event_declarationContext ctx) {
    	DeadlockFunction method = new DeadlockFunction("event_"  + RunnableMethods.size(), currentClass, null, false);
        Pair<List<Integer>, Map<Long, Integer>> pTypes = getMethodParameterTypes(null, method);
        
        method.setMethodMetadata(-1, pTypes.left, pTypes.right);
        methodStack.add(method);
    }
    
    @Override
    public void exitEvent_declaration(CSharpParser.Event_declarationContext ctx) {
    	DeadlockFunction method = methodStack.pop();
        RunnableMethods.add(method);
    }
    
    @Override
    public void enterLocal_variable_declaration(CSharpParser.Local_variable_declarationContext ctx) {
        if (ctx.local_variable_declarator() != null) {
            processLocalVariableDeclaratorId(ctx.local_variable_type().getText(), ctx.local_variable_declarator().get(ctx.local_variable_declarator().size() - 1).identifier().getText(), methodStack.peek());
        }
    }
    
    @Override
    public void enterSpecific_catch_clause(CSharpParser.Specific_catch_clauseContext ctx) {
        if (ctx.identifier() != null) {
            processLocalVariableDeclaratorId("Exception", ctx.identifier().getText(), methodStack.peek());
        }
    }
    
    private void enterElementValuePair(String elementName, String value) {
        String lockName = currentPackageName.peek() + (currentClass != null ? currentClass.getPathName() + ".": "") + elementName;
                
        if(!readLockWaitingSet.isEmpty() || !writeLockWaitingSet.isEmpty()) {
            if(readLockWaitingSet.contains(lockName)) {
                processLock("ReadLock1", elementName, value);
            } else if(writeLockWaitingSet.contains(lockName)) {
                processLock("WriteLock1", elementName, value);
            }
        }
    }
    
    @Override
    public void enterEnum_member_declaration(CSharpParser.Enum_member_declarationContext ctx) {
		enterElementValuePair(ctx.identifier().IDENTIFIER().getText(), ctx.identifier().IDENTIFIER().getText());
    }
    
    @Override
    public void enterArg_declaration(CSharpParser.Arg_declarationContext ctx) {
    	enterElementValuePair(ctx.identifier().IDENTIFIER().getText(), ctx.identifier().IDENTIFIER().getText());
    }
    
    @Override
    public void enterConstant_declarator(CSharpParser.Constant_declaratorContext ctx) {
    	enterElementValuePair(ctx.identifier().IDENTIFIER().getText(), ctx.identifier().IDENTIFIER().getText());
    }
    
    @Override
    public void enterLet_clause(CSharpParser.Let_clauseContext ctx) {
    	if (ctx.expression() != null) {
    		enterElementValuePair(ctx.identifier().IDENTIFIER().getText(), ctx.expression().getChild(0).getText());
    	}
    }
    
    @Override
    public void enterMember_declarator(CSharpParser.Member_declaratorContext ctx) {
    	if (ctx.expression() != null) {
    		enterElementValuePair(ctx.identifier().IDENTIFIER().getText(), ctx.expression().getChild(0).getText());
    	}
    }
    
    private static String getSyncLockName(Integer syncLockId) {
        return "synchLock" + syncLockId;
    }
    
    private static CSharpParser.ExpressionContext generateSyncLockExpression(String syncLockName, boolean lock) {
        String lockStrExpr = syncLockName + "." + (lock ? "lock" : "unlock") + "();";
        CSharpLexer lexer = new CSharpLexer(CharStreams.fromString(lockStrExpr));
        CommonTokenStream commonTokenStream = new CommonTokenStream(lexer);
        CSharpParser parser = new CSharpParser(commonTokenStream);
        
        return parser.expression();
    }
    
    private static void addMethodFromExpression(CSharpParser.Unary_expressionContext ctx) {
        DeadlockFunction mdf = methodStack.peek();
        
        if(!ctx.primary_expression().method_invocation().isEmpty() || !ctx.primary_expression().member_access().isEmpty()) {
            mdf.addMethodCall(ctx);
        }
    }
    
    @Override
    public void enterUnary_expression(CSharpParser.Unary_expressionContext ctx) {
    	runningMethodCallCount.incrementAndGet();
    }
    
    @Override
    public void exitUnary_expression(CSharpParser.Unary_expressionContext ctx) {
        
            int count = runningMethodCallCount.decrementAndGet();

        if(count == 0 && !methodStack.isEmpty() && ctx.primary_expression() != null && ctx.primary_expression().method_invocation().size() > 0) {
            addMethodFromExpression(ctx);
        }
        
    }
    
    // lambda methods
    private static Pair<Integer, Pair<List<Integer>, Map<Long, Integer>>> getMethodMetadata(CSharpParser.Method_declarationContext ctx, DeadlockFunction method) {
        Integer type = getTypeId("void", currentCompleteFileClassName);
        Pair<List<Integer>, Map<Long, Integer>> params = getMethodParameterTypes(ctx.formal_parameter_list(), method);
        
        return new Pair<>(type, params);
    }
    
    private static Pair<Integer, Pair<List<Integer>, Map<Long, Integer>>> getLocalFunctionMetadata(CSharpParser.Local_function_declarationContext ctx, DeadlockFunction method) {
        Integer type = getTypeId(ctx.local_function_header().return_type().getText(), currentCompleteFileClassName);
        Pair<List<Integer>, Map<Long, Integer>> params = getMethodParameterTypes(ctx.local_function_header().formal_parameter_list(), method);
        
        return new Pair<>(type, params);
    }
    
    private static Pair<List<Integer>, Map<Long, Integer>> getMethodParameterTypes(CSharpParser.Formal_parameter_listContext ctx, DeadlockFunction method) {
        Map<Long, Integer> params = new HashMap<>();
        List<Integer> pTypes = new LinkedList<>();
        
        if(ctx != null) {
        	CSharpParser.Parameter_arrayContext aCtx = ctx.parameter_array();
            while(aCtx != null) {
            	String typeText = aCtx.array_type().getText();
            	String nameText = aCtx.identifier().getText();
            	
            	String tt = getFullTypeText(aCtx.array_type().base_type().getText(), typeText);
                int typeId = getTypeId(tt, currentCompleteFileClassName);
                pTypes.add(typeId);
                
                Long val = method.addLocalVariable(typeId, nameText);
                params.put(val, typeId);
                
                aCtx = ctx.parameter_array();
            }
        }
        
        return new Pair<>(pTypes, params);
    }
    
    private static int countOccurrences(String haystack, char needle) {
        int count = 0;
        for (int i=0; i < haystack.length(); i++) {
            if (haystack.charAt(i) == needle) {
                count++;
            }
        }
        return count;
    }
    
    private static String getFullTypeText(String typeText, String curText) {
        String tt = typeText;
            
        int count = countOccurrences(curText, '[');
        for(int i = 0; i < count; i++) {
            tt += "[]";
        }
        
        return tt;
    }
    
    private static void processFieldVariableDeclarations(String typeText, List<String> vdList) {
        if (currentClass != null) {
            for(String vdName : vdList) {
                String tt = getFullTypeText(typeText, vdName);
                int type = getTypeId(tt, currentCompleteFileClassName);

                currentClass.addFieldVariable(type, vdName);
            }
        }
    }
    
    private static void processLocalVariableDeclarations(String typeText, List<String> vdList, DeadlockFunction method) {
        for(String vdName : vdList) {
            processLocalVariableDeclaratorId(typeText, vdName, method);
        }
    }
    
    private static void processLocalVariableDeclaratorId(String typeText, String vdName, DeadlockFunction method) {
        String tt = getFullTypeText(typeText, vdName);    
        int type = getTypeId(tt, currentCompleteFileClassName);
        
        String vdId = vdName;
        int idx = vdId.indexOf('[');
        if (idx > -1) {
        	vdId.substring(0, idx);
        }
        
        method.addLocalVariable(type, vdId);
    }
    
    private static Integer getTypeId(String type, String fileClass) {
        Integer t = runningTypeId.getAndIncrement();
        volatileDataTypes.put(t, new Pair<>(type, fileClass));
        
        return t;
    }
    
    private static void processVariableDeclarations(boolean isFieldVar, String typeText, List<String> vdList) {
        if(typeText.contains("Lock")) {
            for(String vdName : vdList) {
                processLock(typeText, vdName, vdName);
            }
        }
        
        if(isFieldVar) processFieldVariableDeclarations(typeText, vdList);
        else processLocalVariableDeclarations(typeText, vdList, methodStack.peek());
    }
    
    private static Pair<String, String> captureLockNameAndReference(CSharpParser.Member_declaratorContext ctx) {
        String name = "_", reference = "_";
        
        CSharpParser.IdentifierContext c1 = ctx.identifier();
        if (c1 != null) {
        	CSharpParser.ExpressionContext c2 = ctx.expression();
            
            if(c2 != null) {
                if(c2.getText().contains("Lock(")) {	// this is a lock initializer
                	try {
                		name = c1.IDENTIFIER().getText();
                		reference = c2.assignment().unary_expression().primary_expression().identifier().get(0).IDENTIFIER().getText();
                	} catch (NullPointerException e) {}	// do nothing
                    
                    return new Pair<>(name, reference);
                }
            }
        }
        
		return null;
    }
    
    private static void processLock(String typeText, String name, String reference) {
        boolean isRead = typeText.contains("Read");
        boolean isWrite = typeText.contains("Write");

        String lockName = DeadlockStorage.getCanonClassName(currentClass) + "." + name;
        String  refName = DeadlockStorage.getCanonClassName(currentClass) + "." + reference;
        
        //System.out.println("Parsing lock : '" + typeText + "' name: '" + lockName + "' ref: '" + refName + "'");
        
        if(isRead && isWrite) {
            DeadlockLock rwLock = instanceNewLock(lockName);
            
            String queued;
            queued = readLockQueue.remove(lockName);
            if(queued != null) {
                Locks.put(queued, rwLock);
            } else {
                readLockWaitingSet.add(lockName);
            }
            
            queued = writeLockQueue.remove(lockName);
            if(queued != null) {
                Locks.put(queued, rwLock);
            } else {
                writeLockWaitingSet.add(lockName);
            }
            
            ReadWriteLocks.put(lockName, rwLock);
        } else if(isRead) {
            if(reference != null) {
                if(!readLockWaitingSet.remove(refName)) {
                    readLockQueue.put(refName, lockName);
                } else {
                    Locks.put(lockName, ReadWriteLocks.get(refName));
                }
            } else {
                Locks.put(lockName, null);
            }
        } else if(isWrite) {
            if(reference != null) {
                if(!writeLockWaitingSet.remove(refName)) {
                    writeLockQueue.put(refName, lockName);
                } else {
                    Locks.put(lockName, ReadWriteLocks.get(refName));
                }
            } else {
                Locks.put(lockName, null);
            }
        } else {
            Locks.put(lockName, instanceNewLock(lockName));
        }
    }
    
    private static DeadlockLock instanceNewLock(String lockName) {
        return new DeadlockLock(runningId.getAndIncrement(), lockName);
    }
    
    private static DeadlockClass getPublicClass(String packageName, String className) {
        DeadlockClass mdc = PublicClasses.get(packageName).get(className);
        
        //if(mdc == null) System.out.println("FAILED TO FIND PUBLIC '" + className + "' @ '" + packageName + "'");
        return mdc;
    }
    
    private static DeadlockClass getPrivateClass(String packageName, String className) {
        //System.out.println("trying " + packageName + " on " + className);
        Map<String, DeadlockClass> m = PrivateClasses.get(packageName);
        DeadlockClass mdc = (m != null) ? m.get(className) : null;
        
        //if(mdc == null) System.out.println("FAILED TO FIND PRIVATE '" + className + "' @ '" + packageName + "'");
        return mdc;
    }
    
    private static List<DeadlockClass> getAllPrivateClassesWithin(String treeName, Map<String, DeadlockClass> privateMap) {
        List<DeadlockClass> list = new LinkedList<>();
        
        if (privateMap != null) {
            for(Entry<String, DeadlockClass> m : privateMap.entrySet()) {
                if(m.getKey().startsWith(treeName)) {
                    list.add(m.getValue());
                }
            }
        }
        
        return list;
    }
    
    private static boolean isEnumClass(String packageName, String className) {
        DeadlockClass mdc = getPrivateClass(packageName, className);
        if(mdc != null) {
            return mdc.isEnum();
        }
        
        return false;
    }
    
    private static void parseImportClass(DeadlockClass mdc) {
        for(String s : mdc.getImportNames()) {
            Pair<String, String> p = DeadlockStorage.locateClassPath(s);
            if(p != null) {
                String packageName = p.left;
                String className = p.right;

                Map<String, DeadlockClass> m = PublicClasses.get(packageName);

                if(m != null) {
                    mdc.removeImport(s);    // changing full names for class name

                    if(!className.contentEquals("*")) {
                        DeadlockClass importedClass = getPublicClass(packageName, className);
                        mdc.updateImport(importedClass.getPackageName() + importedClass.getPathName(), s, importedClass);
                    } else {
                        for(DeadlockClass packClass : m.values()) {
                            if (mdc != packClass) {
                                mdc.updateImport(packClass.getPackageName() + packClass.getPathName(), s, packClass);
                            }
                        }
                    }
                } else {
                    //System.out.println("\n\nfailed finding " + s + " on PUBLIC");
                    //check private imports in case of failure
                    
                    if(!isEnumClass(packageName, className)) {
                        int idx = className.lastIndexOf('*');
                        if(idx != -1) {
                            s = s.substring(0, idx);

                            for(DeadlockClass packClass : getAllPrivateClassesWithin(className.substring(0, idx - 1), PrivateClasses.get(packageName))) {
                                mdc.updateImport(packClass.getPackageName() + packClass.getPathName(), s, packClass);
                            }
                        } else {
                            DeadlockClass importedClass = getPrivateClass(packageName, className);
                            if(importedClass != null) {
                                mdc.updateImport(importedClass.getPackageName() + importedClass.getPathName(), s, importedClass);
                            }
                        }
                    } else {
                        DeadlockClass importedClass = getPrivateClass(packageName, className);
                        mdc.updateImport(importedClass.getPackageName() + importedClass.getPathName(), s, importedClass);
                    }
                }
            }
        }
    }
    
    private static void parseImportClasses() {
        for(Map<String, DeadlockClass> mdp : PublicClasses.values()) {
            for(DeadlockClass mdc : mdp.values()) {
                parseImportClass(mdc);
            }
        }
        
        for(Entry<String, Map<String, DeadlockClass>> e : PrivateClasses.entrySet()) {
            String pc = e.getKey();
            
            Pair<String, String> p = DeadlockStorage.locateClassPath(pc);
            String packName = p.left;
            String className = p.right;
            
            DeadlockClass mdc = PublicClasses.get(packName).get(className);
            
            for(DeadlockClass c : e.getValue().values()) {
                for(Pair<String, DeadlockClass> s: mdc.getImports()) {
                    if(s.right != null) c.addImport(DeadlockStorage.getCanonClassName(s.right));
                    else c.addImport(s.left);
                }
                
                parseImportClass(c);
            }
        }
    }
    
    private static void parseSuperClasses(Map<String, Map<String, DeadlockClass>> classes) {
        for(Map<String, DeadlockClass> m : classes.values()) {
            for(DeadlockClass mdc : m.values()) {
                DeadlockClass mdc2 = DeadlockStorage.locateClass(DeadlockStorage.getNameFromCanonClass(mdc), mdc);
                
                List<String> superNames = mdc.getSuperNameList();
                for(String supName : superNames) {
                    DeadlockClass parent = mdc.getParent();
                    if(parent != null && mdc2.isInterface() && supName.contentEquals(parent.getName())) {
                        List<DeadlockClass> list = InheritanceTree.get(mdc2);
                        if(list != null) {
                            list.add(parent);
                        }
                    } else {
                        DeadlockClass sup = mdc.getImport(supName);
                        if (mdc2 != sup && sup != null) {
                            mdc2.addSuper(sup);

                            List<DeadlockClass> list = InheritanceTree.get(mdc2);
                            if(list != null) {
                                list.add(sup);
                            }

                            //if(sup == null) System.out.println("NULL SUPER '" + superName + "' FOR '" + mdc.getName() + "'");
                        }
                    }
                }
                
                DeadlockClass parent = mdc2.getParent();
                if(parent != null) {
                    List<DeadlockClass> list = InheritanceTree.get(parent);
                    if(list != null) {
                        list.add(mdc2);
                    }
                }
            }
        }
    }
    
    private static String parseWrappedType(String s) {
        int idx = s.indexOf("extends");     // assumes the extended element
        if(idx > -1) {
            return s.substring(idx + 7);
        }
        
        return s;
    }
    
    private static List<String> getWrappedTypes(String type) {
        List<String> ret = new LinkedList<>();
        
        int st = Math.min(type.indexOf('('), type.indexOf('<')) + 1, en = 0;
        int c = 1;
        for(int i = st; i < type.length(); i++) {
            char ch = type.charAt(i);

            if(ch == ',') {
                if(c == 1) {
                    ret.add(parseWrappedType(type.substring(st, i)));
                    st = i + 1;
                }
            } else if(ch == '(' || ch == '<') {
                c++;
            } else if(ch == ')' || ch == '<') {
                c--;
                en = i;
            }
        }
        
        if(st == en) return null;
        
        ret.add(type.substring(st, en));
        return ret;
    }
    
    private static Integer filterDataType(Integer ret) {
        Integer e = ElementalDataTypes.get(ret);
        if(e != null) ret = e;
        
        return ret;
    }
    
    private static Integer fetchDataType(String type, DeadlockClass pc) {
        List<Integer> compoundType = new LinkedList<>();
        String t = type;
        
        Integer ret = -2;
        DeadlockClass targetClass;     //search for class data type
        
        int idx = type.indexOf('[');
        int c = 0;
        if(idx == -1) {
            List<String> wrapped = getWrappedTypes(type);
            
            if(wrapped != null) {
                for(String s : wrapped) {
                    compoundType.add(fetchDataType(s, pc));
                }
            }
        } else {
            c = countOccurrences(type, '[');
            
            type = type.substring(0, idx);
            t = type;
        }
        
        int en = type.indexOf('(');
        if(en != -1) t = type.substring(0, en);
        
        if (IgnoredTypes.isDataTypeIgnored(t)) {
            return BasicDataTypes.get("Object");
        }
        
        switch (DeadlockAbstractType.getValue(t)) {
            case LOCK:
                return ElementalTypes[5];
                
            case SCRIPT:
                return ElementalTypes[6];
        }
        
        try {
            targetClass = pc.getImport(t);
            if (targetClass == null) {
                String path = DeadlockStorage.getPublicPackageName(pc);
                targetClass = PublicClasses.get(path).get(t);
            }
        } catch(NullPointerException e) {
            if (pc != null) System.out.println("EXCEPTION ON " + t + " ON SRC " + pc.getPackageName() + pc.getPathName());
            targetClass = null;
        }
        
        if(targetClass != null) {
            Integer classId = runningTypeId.get();
            String nameChanged = "";
            if(c > 0) {
                for(int i = 0; i <= c; i++) {
                    ret = BasicDataTypes.get(targetClass.getPackageName() + targetClass.getName() + nameChanged);
                    if(ret == null) {
                        ret = runningTypeId.getAndIncrement();
                        BasicDataTypes.put(targetClass.getPackageName() + targetClass.getName() + nameChanged, ret);
                    }
                    
                    nameChanged += "[]";
                }
            }

            ret = ClassDataTypes.get(targetClass);
            if(ret == null) {
                ret = classId;
                ClassDataTypes.put(targetClass, ret);
            }
            
            if(!compoundType.isEmpty()) {
                compoundType.add(ret);

                ret = CompoundDataTypes.get(compoundType);
                if(ret == null) {
                    ret = runningTypeId.getAndIncrement();
                    //CompoundDataNames.put(ret, type);

                    CompoundDataTypes.put(compoundType, ret);
                }
            }
        } else if(c > 0) {
            for(int i = 0; i < c; i++) {
                t += "[]";
            }

            ret = BasicDataTypes.get(t);
            if(ret == null) {
                ret = runningTypeId.getAndIncrement();
                BasicDataTypes.put(t, ret);
            }
        } else {
            if(!compoundType.isEmpty()) {
                compoundType.add(ret);

                ret = CompoundDataTypes.get(compoundType);
                if(ret == null) {
                    ret = runningTypeId.getAndIncrement();
                    //CompoundDataNames.put(ret, type);
                    
                    CompoundDataTypes.put(compoundType, ret);
                }
            }
        }
        
        return ret;
    }
    
    private static Integer parseDataType(Integer volatileType) {
        if(volatileType <= 0 && volatileType >= -1) {
            return volatileType;
        }
        
        Pair<String, String> p = volatileDataTypes.get(volatileType);
        String type = p.left;
        if(type.contentEquals("void")) return -2;
        
        Integer ret = fetchDataType(type, DeadlockStorage.locateClass(p.right));
        return ret;
    }
    
    private static void updateFunctionReferences(DeadlockFunction f) {
        f.setReturn(parseDataType(f.getReturn()));
                    
        List<Integer> pList = f.getParameters();
        for(int i = 0; i < pList.size(); i++) {
            f.updateParameter(i, parseDataType(pList.get(i)));
        }

        for(Entry<Long, List<Integer>> lv : f.getVolatileLocalVariables().entrySet()) {
            List<Integer> localList = lv.getValue();
            Set<Integer> localTypes = new HashSet<>();

            for(int i = 0; i < localList.size(); i++) {
                Integer type = parseDataType(localList.get(i));

                if(!localTypes.contains(type)) {
                    localTypes.add(type);
                }
            }
            
            f.updateLocalVariable(lv.getKey(), localTypes);
        }

        f.clearVolatileLocalVariables();

        for(Entry<Long, Integer> pv : f.getParameterVariables().entrySet()) {
            f.updateParameterVariable(pv.getKey(), parseDataType(pv.getValue()));
        }
    }
    
    private static void updatePackageReferences(Map<String, Map<String, DeadlockClass>> packageClasses) {
        for(Map<String, DeadlockClass> m : packageClasses.values()) {
            for(DeadlockClass mdc : m.values()) {
                for(Entry<String, Integer> e : mdc.getFieldVariables().entrySet()) {
                    mdc.updateFieldVariable(e.getKey(), parseDataType(e.getValue()));
                }
                
                for(DeadlockFunction f : mdc.getMethods()) {
                    updateFunctionReferences(f);
                }
            }
        }
        
        for(Map<String, DeadlockClass> m : packageClasses.values()) {
            for(DeadlockClass mdc : m.values()) {
                mdc.generateMaskedTypeSet();
            }
        }
    }
    
    private static void parseDataTypes() {
        runningTypeId.set(0);   // id 0 reserved for sync locks
        
        instantiateElementalDataTypes();
        generateElementalDataTypes();
        
        for(Map<String, DeadlockClass> m : PublicClasses.values()) {
            for(DeadlockClass c : m.values()) {
                ClassDataTypes.put(c, runningTypeId.getAndIncrement());
            }
        }
        
        for(Map<String, DeadlockClass> m : PrivateClasses.values()) {
            for(DeadlockClass c : m.values()) {
                ClassDataTypes.put(c, runningTypeId.getAndIncrement());
            }
        }
        
        for(Entry<Integer, Pair<DeadlockClass, Integer>> e : volatileMaskedTypes.entrySet()) {
            if(e != null) {
                e.getValue().left.updateMaskedType(e.getValue().right, parseDataType(e.getKey()));
            }
        }
        
        updatePackageReferences(PublicClasses);
        updatePackageReferences(PrivateClasses);
    }
    
    private static void linkElementalDataTypes(String link, String target) {
        Integer typeId = runningTypeId.getAndIncrement();
        
        BasicDataTypes.put(link, typeId);
        ElementalDataTypes.put(typeId, BasicDataTypes.get(target));
        LinkedDataNames.put(typeId, target);
    }
    
    private static void instantiateElementalDataType(String s) {
        BasicDataTypes.put(s, runningTypeId.getAndIncrement());
    }
    
    private static void instantiateIgnoredDataTypes() {
        Integer start = runningTypeId.get();
        
        for(String s : IgnoredTypes.getIgnoredTypes()) {
            instantiateElementalDataType(s);
        }
        
        storage.setIgnoredDataRange(new Pair<>(start, runningTypeId.get()));
    }
    
    private static void generateReflectedDataTypes() {
        for(ReflectedTypes mrt : ReflectedTypes.getReflectedTypes()) {
            Integer mrtId = BasicDataTypes.get(mrt.getName());
            Integer mrtDefReturn = BasicDataTypes.get(mrt.getDefaultReturn());
            Map<String, Integer> mrtMethods = new HashMap<>();
            
            for(Entry<String, String> emrt : mrt.getMethodReturns().entrySet()) {
                mrtMethods.put(emrt.getKey(), BasicDataTypes.get(emrt.getValue()));
            }
            
            ReflectedClasses.put(mrtId, new Pair<>(mrtDefReturn, mrtMethods));
        }
    }
    
    private static void instantiateElementalDataTypes() {
        instantiateElementalDataType(syncLockTypeName);
        
        // basic language types
        instantiateElementalDataType("int");
        instantiateElementalDataType("float");
        instantiateElementalDataType("char");
        instantiateElementalDataType("String");
        instantiateElementalDataType("boolean");
        instantiateElementalDataType("null");
        instantiateElementalDataType("byte");
        
        instantiateElementalDataType("int[]");
        instantiateElementalDataType("long[]");
        
        // basic abstract data types
        instantiateElementalDataType("Set");
        instantiateElementalDataType("List");
        instantiateElementalDataType("Map");
        instantiateElementalDataType("Lock");
        instantiateElementalDataType("Invocable");
        
        instantiateIgnoredDataTypes();
    }
    
    private static void generateElementalDataTypes() {
        ElementalTypes[0] = BasicDataTypes.get("int");
        ElementalTypes[1] = BasicDataTypes.get("int");    // float, but let numbers have the same data reference for the sake of simplicity
        ElementalTypes[2] = BasicDataTypes.get("char");
        ElementalTypes[3] = BasicDataTypes.get("String");
        ElementalTypes[4] = BasicDataTypes.get("boolean");
        ElementalTypes[5] = BasicDataTypes.get("Lock");
        ElementalTypes[6] = BasicDataTypes.get("Invocable");
        ElementalTypes[7] = BasicDataTypes.get("null");
        
        for(Pair<String, String> p : LinkedTypes.getLinkedTypes()) {
            linkElementalDataTypes(p.left, p.right);
        }
    }
    
    private static void generateDereferencedDataTypes() {
        for(Entry<String, Integer> e : BasicDataTypes.entrySet()) {
            String s = e.getKey();
            
            int c = countOccurrences(s, '[');
            if(c > 0) {
                DeadlockClass targetClass = DeadlockStorage.locatePublicClass(s.substring(0, s.indexOf('[')), null);
                if (targetClass != null) {
                    String nameChanged = "";
                    for(int i = 0; i < c; i++) {
                        nameChanged += "[]";
                    }

                    if(nameChanged.length() > 0) {
                        Integer i = BasicDataTypes.get(targetClass.getPackageName() + targetClass.getName() + nameChanged);
                        if(i == null) {
                            i = runningTypeId.getAndIncrement();
                            BasicDataTypes.put(targetClass.getPackageName() + targetClass.getName() + nameChanged, i);
                        }
                    }
                } else {
                    Integer i = BasicDataTypes.get(s);
                    if(i == null) {
                        i = runningTypeId.getAndIncrement();
                        BasicDataTypes.put(s, i);
                    }
                }
            }
        }
    }
    
    public static void solveRunnableFunctions() {
        for(Entry<DeadlockFunction, Boolean> runMdf : RunnableFunctions.entrySet()) {
            DeadlockFunction mdf = runMdf.getKey();
            updateFunctionReferences(mdf);
            
            DeadlockClass mdc = mdf.getSourceClass();
            if(runMdf.getValue() || mdc.getSuperNameList().contains("Runnable")) {
                RunnableMethods.add(mdf);
            }
            
            mdc.addClassMethod(mdf);
        }
    }
    
    private static void referenceCustomClasses() {
        for (DeadlockClass c : customClasses) {
            DeadlockClass sup = DeadlockStorage.locateClass(c.getName(), c);
            c.addSuper(sup);
        }
        customClasses.clear();
    }
    
    private static void referenceReadWriteLocks() {
        for (Entry<String, DeadlockLock> e : ReadWriteLocks.entrySet()) {
            Locks.put(e.getKey(), e.getValue());
        }
    }
    
    public static DeadlockStorage compileProjectData() {
        //System.out.println(storage);
        
        parseImportClasses();
        
        parseSuperClasses(PublicClasses);
        parseSuperClasses(PrivateClasses);
        
        Map<String, Map<String, DeadlockClass>> m = new HashMap<>();
        Map<String, DeadlockClass> n = new HashMap<>();
        
        m.put("", n);
        for(DeadlockClass c : customClasses) {
            n.put(c.getName(), c);
        }
        parseSuperClasses(m);
        
        referenceCustomClasses();
        referenceReadWriteLocks();
        
        /*
        for(Entry<Integer, Pair<String, String>> v : volatileDataTypes.entrySet()) {
            System.out.println(v.getKey() + " : " + v.getValue());
        }
        
        for(Map<String, DeadlockClass> o : PublicClasses.values()) {
            for(DeadlockClass mdc : o.values()) {
                System.out.println(mdc);
            }
        }
        
        for(Map<String, DeadlockClass> o : PrivateClasses.values()) {
            for(DeadlockClass mdc : o.values()) {
                System.out.println(mdc);
            }
        }
        */
        
        parseDataTypes();
        fetchDataType("Set<Object>", null);
        
        generateDereferencedDataTypes();
        generateReflectedDataTypes();
        
        solveRunnableFunctions();
        
        return storage;
    }
}
