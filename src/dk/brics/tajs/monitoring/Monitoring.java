/*
 * Copyright 2009-2016 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package dk.brics.tajs.monitoring;

import dk.brics.tajs.analysis.js.UserFunctionCalls;
import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.BasicBlock;
import dk.brics.tajs.flowgraph.FlowGraph;
import dk.brics.tajs.flowgraph.Function;
import dk.brics.tajs.flowgraph.HostEnvSources;
import dk.brics.tajs.flowgraph.SourceLocation;
import dk.brics.tajs.flowgraph.jsnodes.AssumeNode;
import dk.brics.tajs.flowgraph.jsnodes.BeginForInNode;
import dk.brics.tajs.flowgraph.jsnodes.BeginLoopNode;
import dk.brics.tajs.flowgraph.jsnodes.BeginWithNode;
import dk.brics.tajs.flowgraph.jsnodes.BinaryOperatorNode;
import dk.brics.tajs.flowgraph.jsnodes.CallNode;
import dk.brics.tajs.flowgraph.jsnodes.CatchNode;
import dk.brics.tajs.flowgraph.jsnodes.ConstantNode;
import dk.brics.tajs.flowgraph.jsnodes.DeclareFunctionNode;
import dk.brics.tajs.flowgraph.jsnodes.DeclareVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.DeletePropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.EndForInNode;
import dk.brics.tajs.flowgraph.jsnodes.EndLoopNode;
import dk.brics.tajs.flowgraph.jsnodes.EndWithNode;
import dk.brics.tajs.flowgraph.jsnodes.EventDispatcherNode;
import dk.brics.tajs.flowgraph.jsnodes.ExceptionalReturnNode;
import dk.brics.tajs.flowgraph.jsnodes.HasNextPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.IfNode;
import dk.brics.tajs.flowgraph.jsnodes.NewObjectNode;
import dk.brics.tajs.flowgraph.jsnodes.NextPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.Node;
import dk.brics.tajs.flowgraph.jsnodes.NodeVisitor;
import dk.brics.tajs.flowgraph.jsnodes.NopNode;
import dk.brics.tajs.flowgraph.jsnodes.ReadPropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.ReadVariableNode;
import dk.brics.tajs.flowgraph.jsnodes.ReturnNode;
import dk.brics.tajs.flowgraph.jsnodes.ThrowNode;
import dk.brics.tajs.flowgraph.jsnodes.TypeofNode;
import dk.brics.tajs.flowgraph.jsnodes.UnaryOperatorNode;
import dk.brics.tajs.flowgraph.jsnodes.WritePropertyNode;
import dk.brics.tajs.flowgraph.jsnodes.WriteVariableNode;
import dk.brics.tajs.lattice.CallEdge;
import dk.brics.tajs.lattice.Context;
import dk.brics.tajs.lattice.HostObject;
import dk.brics.tajs.lattice.Obj;
import dk.brics.tajs.lattice.ObjectLabel;
import dk.brics.tajs.lattice.ObjectLabel.Kind;
import dk.brics.tajs.lattice.ScopeChain;
import dk.brics.tajs.lattice.State;
import dk.brics.tajs.lattice.Str;
import dk.brics.tajs.lattice.UnknownValueResolver;
import dk.brics.tajs.lattice.Value;
import dk.brics.tajs.monitoring.ObjReadsWrites.R_Status;
import dk.brics.tajs.monitoring.ObjReadsWrites.W_Status;
import dk.brics.tajs.options.Options;
import dk.brics.tajs.solver.CallGraph;
import dk.brics.tajs.solver.Message;
import dk.brics.tajs.solver.Message.Severity;
import dk.brics.tajs.solver.Message.Status;
import dk.brics.tajs.solver.NodeAndContext;
import dk.brics.tajs.util.AnalysisException;
import dk.brics.tajs.util.Pair;
import dk.brics.tajs.util.Strings;
import org.apache.log4j.Logger;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.NumberFormat;
import java.util.*;
import java.util.Map.Entry;

import static dk.brics.tajs.util.Collections.addAllToMapSet;
import static dk.brics.tajs.util.Collections.addToMapList;
import static dk.brics.tajs.util.Collections.addToMapSet;
import static dk.brics.tajs.util.Collections.newList;
import static dk.brics.tajs.util.Collections.newMap;
import static dk.brics.tajs.util.Collections.newSet;

/**
 * Records various information during analysis.
 */
public class Monitoring implements IAnalysisMonitoring {

    public Set<CallNode> parameterArgumentMismatch = newSet();
    public Set<IfNode> conditionalAssignments = newSet();
    public Set<DeclareFunctionNode> longParameterList = newSet();
    public Set<ReadVariableNode> nestedCallbackNodes = newSet();
    public Set<ReadPropertyNode> extraBindNodes = newSet();
    public static ArrayList<Function> nested_callbacks = new ArrayList();
    public Set<CatchNode> emptyCatchNodes = newSet();
    public Set<IfNode> switchNodes = newSet();
    public Set<String> lengthyVariableNames = newSet();
    public Set<BasicBlock> observedBlocks = newSet();
    public int lengthVariableCount;
    String results = "";
    public static Set<DeclareFunctionNode> longMethods = newSet();
    public Set<IfNode> nestedIfs = newSet();
    public Set<CallNode> subsequentCallNodes = newSet();
    public static Set<IfNode> conditionalIfs = newSet();
    public static Set<String> mainGlobalVariables = newSet();
    public int callNestCount;
    public Set<AbstractNode> nestedCalls = newSet();
    public Set<CallNode> constructorCalls = newSet();
    private int parameterNum;
    private int argumentNum;
    public static Set<BasicBlock> visitedBlocks = newSet();
    public Set<BasicBlock> loopBlocks = newSet();
    public int depthCount = 0;
    private static Logger log = Logger.getLogger(Monitoring.class);

    /**
     * Set if in scan phase (at the fixpoint).
     */
    private boolean scan_phase = false;

    /**
     * Number of node transfers.
     */
    private int node_transfers = 0;

    /**
     * Number of block transfers.
     */
    private int block_transfers = 0;

    /**
     * Number of calls to the UnknownValueResolver where a value is recovered partially in non-scanning mode.
     */
    private int unknown_value_resolve_analyzing_partial = 0;

    /**
     * Number of calls to the UnknownValueResolver where a value is recovered fully in non-scanning mode.
     */
    private int unknown_value_resolve_analyzing_full = 0;

    /**
     * Number of calls to the UnknownValueResolver where a value is recovered partially in scanning mode.
     */
    private int unknown_value_resolve_scanning_partial = 0;

    /**
     * Number of calls to the UnknownValueResolver where a value is recovered fully in scanning mode.
     */
    private int unknown_value_resolve_scanning_full = 0;

    /**
     * Number of abstract state join operations.
     */
    private int joins = 0;

    /**
     * Reachable functions.
     */
    private Set<Function> reachable_functions;

    /**
     * All functions
     */
    private Set<Function> functions;

    /**
     * Number of (non-this) variable read operations.
     */
    private int read_variable_nodes = 0;

    /**
     * Number of property access operations.
     */
    private int property_access_nodes = 0;

    /**
     * Number of fixed-property read operations.
     */
    private int read_fixed_property_nodes = 0;

    /**
     * Number of call/construct nodes.
     */
    private int call_nodes = 0;

    /**
     * Variable read operations that may read an absent variable.
     */
    private Set<ReadVariableNode> absent_variable_read;

    /**
     * Fixed-property read operations that may access an absent property.
     */
    private Set<ReadPropertyNode> absent_fixed_property_read;

    /**
     * Property access operations that may dereference null or undefined.
     */
    private Set<Node> null_undef_base;

    /**
     * Call/construct nodes that may involve non-function values.
     */
    private Set<AbstractNode> call_to_non_function;

    /**
     * Store information about values read during analysis.
     */
    private Map<NodeAndContext<Context>, Value> value_reads;

    /**
     * Values passed to eval.
     */
    private Map<AbstractNode, Value> eval_calls;

    /**
     * Values written to innerHTML.
     */
    private Map<AbstractNode, Value> inner_html_writes;

    /**
     * Descriptions of new dataflow at function entry blocks.
     */
    private Map<BasicBlock, Map<Context, List<String>>> newflows;

    /**
     * Maximum memory usage measured.
     */
    private long max_memory = 0;

    /**
     * Map from line URL to set of guaranteed undefined lines in the source text.
     */
    private Map<String, Set<Integer>> unreachable_lines;

    /**
     * Information about read/written properties in all abstract objects.
     * Singleton/summary information is stored for the singleton variant.
     */
    private Map<ObjectLabel, ObjReadsWrites> obj_reads_writes;

    /**
     * Variables and parameters that are declared in each function and maybe read.
     * Undeclared variables belong to the main function.
     */
    private Map<Function, Set<String>> read_variables;

    /**
     * All reachable nodes.
     */
    private Set<AbstractNode> reachable_nodes;

    /**
     * Functions that may be called as constructors.
     */
    private Set<Function> called_as_constructor;

    private TypeCollector type_collector;

//    /**
//     * Counter for {@link #visitNewFlow(BasicBlock, IContext, IState, String, String)}.
//     */
//    private int next_newflow_file;

    /**
     * Number of property recovery graphs of different sizes.
     */
    private Map<Integer, Integer> recovery_graph_sizes;

    /**
     * Collected messages.
     * Maps each message object to itself to make it possible to find existing messages that are "equal" to new ones.
     */
    private Map<Message, Message> messages;

    /**
     * The current flowgraph
     */
    private FlowGraph flowgraph;

    /**
     * The current callgraph
     */
    private CallGraph<State, Context, CallEdge> callgraph;

    /**
     * Constructs a new monitoring object.
     */
    public Monitoring() {
        call_to_non_function = newSet();
        absent_variable_read = newSet();
        null_undef_base = newSet();
        absent_fixed_property_read = newSet();
        newflows = newMap();
        eval_calls = newMap();
        inner_html_writes = newMap();
        unreachable_lines = newMap();
        value_reads = newMap();
        obj_reads_writes = newMap();
        read_variables = newMap();
        reachable_functions = newSet();
        functions = newSet();
        reachable_nodes = newSet();
        called_as_constructor = newSet();
        type_collector = new TypeCollector();
        recovery_graph_sizes = newMap();
//        next_newflow_file = 1;
        messages = null;
    }

    public String reportLongMethods() {
        String msg = "********Long Methods********\r\n";
        msg += "Number of occurences: " + longMethods.size() + "\r\n";
        for (DeclareFunctionNode dfn: longMethods) {
            addMessage(dfn, Status.CERTAIN, Severity.MEDIUM, "Method is too long");
            msg += "Function: " + dfn.getFunction().getName() + " at line number: " + dfn.getSourceLocation().getLineNumber() + "\r\n";
        }
        return msg;
    }

    public String reportParameterArgumentMismatch() {
        String msg = "********Parameter Argument Mismatch********\r\n";
        String output = "";
        int count = 0;
        for(CallNode n: UserFunctionCalls.Arg_Mismatches) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Parameter/Argument Mismatch");
            output += "Instance at line: " + n.getSourceLocation().getLineNumber() + "\r\n";
            count++;
        }
        msg += "Number of occurences: " + count + "\r\n";
        msg += output;
        return msg;
    }

    public String reportNestedIfs() {
        String msg = "********Excessive Nesting********\r\n";
        msg += "Number of occurences: " + nestedIfs.size() + "\r\n";
        for (IfNode n: nestedIfs) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Too many nested if/for/while statements");
            msg += "Occurance at line number: " + n.getSourceLocation().getLineNumber() + "\r\n";
        }
        return msg;
    }

    public boolean findSwitch(IfNode n) {
        BasicBlock currentBlock = n.getBlock();
        int caseCount = 0;
        do{
            if (currentBlock.getLastNode() instanceof IfNode) {
                currentBlock = ((IfNode) currentBlock.getLastNode()).getSuccFalse();
                if (currentBlock.getLastNode().getSourceLocation() == n.getSourceLocation())
                    caseCount++;
            }
        } while (currentBlock.getLastNode() instanceof IfNode);
        if (caseCount > 2) {
            return true;
        }
        else
            return false;
    }

    public int findMessageDepth(ReadVariableNode n) {
        List<AbstractNode> nodes = n.getBlock().getNodes();
        List<ReadPropertyNode> subsequentNodes = newList();
        BasicBlock currentBlock = n.getBlock();
        int count = 0;
        int resultRegister = n.getResultRegister();
        for (int j = 0; j < nodes.size(); j++) {
            AbstractNode currentNode = nodes.get(j);
            if (currentNode instanceof ReadPropertyNode)
                if (((ReadPropertyNode)currentNode).getBaseRegister() == resultRegister) {
                    if ((((ReadPropertyNode)currentNode).getPropertyString()) != null)
                        count++;
                    resultRegister = ((ReadPropertyNode)currentNode).getResultRegister();
                }
            if (currentNode instanceof WritePropertyNode)
                if (((WritePropertyNode)currentNode).getBaseRegister() == resultRegister) {
                    if ((((WritePropertyNode)currentNode).getPropertyString()) != null)
                        count++;
                    resultRegister = ((WritePropertyNode)currentNode).getPropertyRegister();
                }
            if (count > 2) {
                if (currentNode.getSourceLocation().getLineNumber() == n.getSourceLocation().getLineNumber())
                    nestedCalls.add(n);
            }
        }
        return count;
    }

    public int findConditionalIfs(IfNode n) {
        if (n.getSuccTrue().getNodes().size() == 1 && n.getSuccTrue().getLastNode() instanceof IfNode) {
            conditionalIfs.add(((IfNode)n.getSuccTrue().getLastNode()));
            return 1;
        }
        else if (n.getSuccFalse().getNodes().size() == 1 && n.getSuccFalse().getLastNode() instanceof IfNode) {
            conditionalIfs.add(((IfNode) n.getSuccTrue().getLastNode()));
            return 0;
        }
        else
            return -1;
    }

    /**
     * Finds the block at which the true and false paths of an if node meet
     * If for/while loop, returns the block of the if node-
     */
    private BasicBlock findConvergentBlock (IfNode n) {
        if (n.getSuccFalse() == n.getSuccTrue())
            return n.getSuccFalse();
        if (searchSucc(n.getBlock())) {
            return n.getBlock();
        }
        Set<BasicBlock> trueBlocks = newSet();
        BasicBlock currentBlock = n.getBlock();
        do {
            trueBlocks.add(currentBlock);
            if (searchSucc(currentBlock))
                currentBlock = ((IfNode)currentBlock.getLastNode()).getSuccFalse();
            else if (currentBlock.getLastNode() instanceof IfNode)
                currentBlock = ((IfNode) currentBlock.getLastNode()).getSuccTrue();
            else
                currentBlock = currentBlock.getSingleSuccessor();
        } while (!(currentBlock.getFirstNode() instanceof ReturnNode) && !trueBlocks.contains(currentBlock));
        currentBlock = n.getSuccFalse();
        do {
            if (trueBlocks.contains(currentBlock)) {
               return currentBlock;
            }
            else if (currentBlock.getLastNode() instanceof IfNode)
                currentBlock = ((IfNode)currentBlock.getLastNode()).getSuccFalse();
            else if (currentBlock.getLastNode() instanceof ReturnNode) {
                return currentBlock;
            }
            else
                currentBlock = currentBlock.getSingleSuccessor();
        } while (currentBlock.getSuccessors().size() != 0);
        return n.getBlock();
    }

    /*
    private BasicBlock findConvergentBlock (IfNode n) {
        if (searchSucc(n.getBlock(), n.getBlock()))
            return n.getBlock();
        Set<BasicBlock> trueBlocks = newSet();
        BasicBlock currentBlock = n.getSuccTrue();
        do  {
            if (currentBlock.getLastNode() instanceof IfNode) {
                switch (findConditionalIfs(((IfNode)currentBlock.getLastNode()))) {
                    case -1:
                        currentBlock = ((IfNode) currentBlock.getLastNode()).getSuccTrue();
                        break;
                    case 0:
                        currentBlock = (((IfNode)((IfNode) currentBlock.getLastNode()).getSuccFalse().getLastNode()).getSuccTrue());
                        break;
                    case 1:
                        currentBlock = (((IfNode)((IfNode) currentBlock.getLastNode()).getSuccTrue().getLastNode()).getSuccTrue());
                        break;
                    default:
                        break;
                }
            }
            else
                currentBlock = currentBlock.getSingleSuccessor();
            trueBlocks.add(currentBlock);
        } while (!(currentBlock.getFirstNode() instanceof ReturnNode) && !trueBlocks.contains(currentBlock));
        currentBlock = n.getSuccFalse();
        do {
            if (currentBlock.getLastNode() instanceof IfNode)
                currentBlock = ((IfNode) currentBlock.getLastNode()).getSuccFalse();
            else
                if (!(currentBlock.getLastNode() instanceof ReturnNode))
                    currentBlock = currentBlock.getSingleSuccessor();
            if ( trueBlocks.contains(currentBlock))
                return currentBlock;
        } while (!(currentBlock.getFirstNode() instanceof ReturnNode));
        return n.getBlock();
    }
*/

    private boolean beginFindDepth(BasicBlock keyBlock) {
        depthCount = 0;
        BasicBlock currentBlock = getFunctionEntryBlock(keyBlock);
        do {
            if (currentBlock == keyBlock)
                return true;
            if (currentBlock.getLastNode() instanceof IfNode) {
                if (findDepth2(currentBlock, keyBlock)) {
                    depthCount++;
                    return true;
                }
                else
                    currentBlock = ((IfNode)currentBlock.getLastNode()).getSuccFalse();
            }
            else
                currentBlock = currentBlock.getSingleSuccessor();
        } while (!(currentBlock.getLastNode() instanceof ReturnNode));
        return false;
    }

    private boolean findDepth2(BasicBlock searchBlock, BasicBlock keyBlock) {
        BasicBlock trueBlock = ((IfNode)searchBlock.getLastNode()).getSuccTrue();
        try{
            if (((IfNode)trueBlock.getLastNode()).getSuccTrue() == ((IfNode)trueBlock.getLastNode()).getSuccFalse())
                return false;
        } catch(Exception e) {}
        try{
            BasicBlock testBlock = ((IfNode)searchBlock.getLastNode()).getSuccFalse();
            testBlock = ((IfNode)searchBlock.getLastNode()).getSuccFalse();
            while (!(testBlock.getFirstNode() instanceof ReturnNode) || !(testBlock.getLastNode() instanceof IfNode)) {
                for (AbstractNode nodes : testBlock.getNodes())
                    if (nodes instanceof NopNode)
                        return false;
                testBlock = testBlock.getSingleSuccessor();
            }
        } catch(AnalysisException ae) {}
        observedBlocks.add(searchBlock);
        BasicBlock convergentBlock = findConvergentBlock((IfNode)searchBlock.getLastNode());
        BasicBlock currentBlock = ((IfNode)searchBlock.getLastNode()).getSuccTrue();
        while (currentBlock != convergentBlock && !observedBlocks.contains(currentBlock)) {
            observedBlocks.add(currentBlock);
            if (currentBlock == keyBlock) {
                depthCount++;
                return true;
            }
            if (currentBlock.getLastNode() instanceof IfNode) {
                if (findDepth2(currentBlock, keyBlock)) {
                    depthCount++;
                    return true;
                } else
                    currentBlock = ((IfNode) currentBlock.getLastNode()).getSuccFalse();
            } else if (currentBlock.getLastNode() instanceof ReturnNode)
                return false;
            else
                currentBlock = currentBlock.getSingleSuccessor();
        }
        return false;
    }


    private boolean findDepth(BasicBlock searchBlock, BasicBlock keyBlock) {
        BasicBlock convergentBlock = keyBlock;
        if (searchBlock.getLastNode() instanceof IfNode) {
            if (searchSucc(searchBlock))
                convergentBlock = searchBlock;
            else
                convergentBlock = findConvergentBlock(((IfNode) searchBlock.getLastNode()));
        }
        if (searchBlock == keyBlock) {
            return true;
        }
        BasicBlock currentBlock = searchBlock;
        for (BasicBlock b: currentBlock.getSuccessors()) {
            if (searchSucc(searchBlock))
                if (b == ((IfNode)searchBlock.getLastNode()).getSuccFalse())
                    continue;
            currentBlock = b;
            while (!(currentBlock.getLastNode() instanceof ReturnNode) && currentBlock != convergentBlock && !observedBlocks.contains(currentBlock)) {
                observedBlocks.add(currentBlock);
                //System.out.println("Current block: " + currentBlock.getIndex() + " with searchblock " + searchBlock.getIndex() + " and keyblock " + keyBlock.getIndex());
                if (currentBlock.getLastNode() instanceof IfNode)
                    try {
                        if (findDepth(currentBlock, keyBlock)) {
                            depthCount++;
                            return true;
                        } else
                            currentBlock = findConvergentBlock(((IfNode) currentBlock.getLastNode()));
                    } catch(StackOverflowError soe) {}
                else
                    currentBlock = currentBlock.getSingleSuccessor();
            }
        }
        return false;
    }

    private boolean searchSucc(BasicBlock keyBlock) {
        if (keyBlock.getFirstNode() instanceof HasNextPropertyNode)
            return true;
        if (!(keyBlock.getLastNode() instanceof IfNode))
            return false;
        BasicBlock currentBlock = ((IfNode) keyBlock.getLastNode()).getSuccTrue();
        while (!(currentBlock.getLastNode() instanceof ReturnNode)) {
            if (currentBlock.getLastNode() instanceof IfNode)
                currentBlock = ((IfNode)currentBlock.getLastNode()).getSuccFalse();
            else
                currentBlock = currentBlock.getSingleSuccessor();
            if (currentBlock == keyBlock)
                return true;
        }
        return false;
    }
    /*
    private boolean searchSucc(BasicBlock keyBlock, BasicBlock searchBlock) {
        if (loopBlocks.contains(searchBlock))
            return false;
        visitedBlocks.add(searchBlock);
        try {
            if (searchBlock.getSingleSuccessor().equals(keyBlock))
                return true;
            else
            if (!visitedBlocks.contains(searchBlock.getSingleSuccessor()));
            return searchSucc(keyBlock, searchBlock.getSingleSuccessor());
        }
        catch (AnalysisException ae) {
            if (searchBlock.getSuccessors().size() == 0)
                return false;
            for (BasicBlock b : searchBlock.getSuccessors()) {
                if (!visitedBlocks.contains(b))
                    if (searchSucc(keyBlock, b))
                        return true;
            }
        }
        catch (StackOverflowError soe) {
            return false;
        }
        return false;
    } */

    public void reportAlreadyDeclaredVariables() {
        for (Function f: FlowGraph.getFunctions())
            for (AbstractNode n: f.alreadyDeclaredVariables)
                addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Already declared variable " + getVariableName(n));
    }

    public String reportReassignedVariable() {
        String msg = "********Variable Re-Assignment********\r\n";
        String output = "";
        int count = 0;
        for (Function f: FlowGraph.getFunctions())
            for (WriteVariableNode n: f.reassignedVariables) {
                addMessage(n, Status.CERTAIN, Severity.MEDIUM, n.getVariableName() + " gets type re-assigned");
                output += "Variable " + n.getVariableName() + " gets type re-assigned at line number: " + n.getSourceLocation().getLineNumber() +  "\r\n";
                count++;
            }
        msg += "Number of occurences: " + count + "\r\n";
        msg += output;
        return msg;
    }

    public String writeVariableNames(AbstractNode n) {
        if (getVariableName(n).length() <= 3) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Short variable name: " + getVariableName(n));
            lengthVariableCount++;
            return "Short Variable: " + getVariableName(n) + " at line number: " + n.getSourceLocation().getLineNumber() + "\r\n";
        }
        else if (getVariableName(n).length() >= 20) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Lengthy variable name: " + getVariableName(n));
            lengthVariableCount++;
            return "Long Variable: " + getVariableName(n) + " at line number: " + n.getSourceLocation().getLineNumber() + "\r\n";
        }
        return "";
    }

    public String reportVariableNames() {
        String msg = "********Short/Long Variable Names********\r\n";
        String output = "";
        lengthVariableCount = 0;
        for (Function f: FlowGraph.getFunctions()) {
            for (AbstractNode n : f.undeclaredFunctionVariables) {
                if (!f.loopVariablesString.contains(getVariableName(n)) && lengthyVariableNames.add(getVariableName(n)))
                    output += writeVariableNames(n);
            }
            for (AbstractNode n : f.declaredFunctionVariables) {
                if (!f.loopVariablesString.contains(getVariableName(n)) && lengthyVariableNames.add(getVariableName(n)))
                    output += writeVariableNames(n);
            }
            for (AbstractNode n : f.functionProperties) {
                if (!f.loopVariablesString.contains(getVariableName(n)) && lengthyVariableNames.add(getVariableName(n)))
                    output += writeVariableNames(n);
            }
        }
        msg += "Number of occurences: " + lengthVariableCount + "\r\n";
        msg += output;
        return msg;
    }

    public BasicBlock getFunctionEntryBlock (BasicBlock block) {
        int index = block.getIndex();
        BasicBlock returnBlock = block;
        Function f = block.getFunction();
        for (BasicBlock b: f.getBlocks())
            if (b.getIndex() < index) {
                index = b.getIndex();
                returnBlock = b;
            }
        return returnBlock;
    }
    public String getVariableName(AbstractNode n) {
        if (n instanceof WriteVariableNode)
            return (((WriteVariableNode)n).getVariableName());
        else if (n instanceof ReadVariableNode)
            return (((ReadVariableNode)n).getVariableName());
        else if (n instanceof WritePropertyNode)
            return (((WritePropertyNode)n).getPropertyString());
        else if (n instanceof ReadPropertyNode)
            return (((ReadPropertyNode)n).getPropertyString());
        else
            return (((DeclareVariableNode)n).getVariableName());
    }

    public void parArgMismatch(CallNode n)
    {
        argumentNum = n.getNumberOfArgs();
        if(parameterNum != argumentNum)
        {
            parameterArgumentMismatch.add(n);
        }
    }

    public boolean extraBind(ReadPropertyNode n)
    {

        for(int i=0; i < n.getBlock().getNodes().size()-1; ++i)
        {
            if(n.getBlock().getNodes().get(i) instanceof DeclareFunctionNode && n.getBlock().getNodes().get(i+1) instanceof ReadPropertyNode) {
                if (((ReadPropertyNode) n.getBlock().getNodes().get(i + 1)).getPropertyString() != null){
                    if (((ReadPropertyNode) n.getBlock().getNodes().get(i + 1)).getPropertyString().equals("bind")) {

                        if (containsThis((DeclareFunctionNode) n.getBlock().getNodes().get(i))) {
                            return false;
                        } else if (!containsThis((DeclareFunctionNode) n.getBlock().getNodes().get(i))) {
                            return true;
                        }
                    }
                }
            }



            if(n.getBlock().getNodes().get(i) instanceof ReadVariableNode && n.getBlock().getNodes().get(i+1) instanceof ReadPropertyNode) {

                if (((ReadPropertyNode) n.getBlock().getNodes().get(i + 1)).getPropertyString() != null){
                    if (((ReadPropertyNode) n.getBlock().getNodes().get(i + 1)).getPropertyString().equals("bind")) {

                        if (containsThis(getFunctionFromWrite((ReadVariableNode) n.getBlock().getNodes().get(i), i))) {

                            return false;
                        } else if (!containsThis(getFunctionFromWrite((ReadVariableNode) n.getBlock().getNodes().get(i), i))) {
                            return true;
                        }
                    }
                }

            }

        }
        return false;
    }


    public DeclareFunctionNode getFunctionFromWrite(ReadVariableNode n, int position)
    {
        String name = n.getVariableName();
        int index = position;
        BasicBlock block = n.getBlock();
        AbstractNode traverseNode;
        AbstractNode traverseNode2;
        int numOfBlocks;

        if(n.getBlock().getFunction().hasOuterFunction())
        {
            ArrayList<BasicBlock> blocks =  (ArrayList<BasicBlock>) block.getFunction().getOuterFunction().getBlocks();
            numOfBlocks = blocks.size();
            for(BasicBlock b : blocks)
            {
                if(b.getIndex() == (numOfBlocks -1))
                {
                    block = b;
                    index = block.getNodes().size()-1;
                }
            }
        }

        while(block != null) {
            for(int i=index;i>0;--i){

                traverseNode=block.getNodes().get(i);
                traverseNode2=block.getNodes().get(i-1);
                if(traverseNode instanceof WriteVariableNode){

                    if(((WriteVariableNode) traverseNode).getVariableName().equals(name) && traverseNode2 instanceof DeclareFunctionNode){

                        return (DeclareFunctionNode) traverseNode2;
                    }
                    else if(((WriteVariableNode) traverseNode).getVariableName().equals(name) && !(traverseNode2 instanceof DeclareFunctionNode))
                    {
                        return null;
                    }

                }

            }

            block = getPreviousBlock(block);
            if(block!=null) {
                index = block.getNodes().size() - 1;
            }

        }
        return null;
    }


    public BasicBlock getPreviousBlock(BasicBlock block){

        for(BasicBlock b : block.getFunction().getBlocks()) {
            if(b.getIndex() == (block.getIndex()-1))
            {
                return b;
            }

        }
        if(block.getIndex()==0)
        {
            return null;
        }
        return null;
    }


    public boolean containsThis(DeclareFunctionNode d)
    {
        if(d==null)
        {
            return false;
        }
        for(BasicBlock b: d.getFunction().getBlocks())
        {

            for(AbstractNode n: b.getNodes())
            {
                //if(((n instanceof ReadVariableNode) && (((ReadVariableNode) n).getVariableName().equals("this")))) {
                if(n instanceof ReadVariableNode){
                    if(((ReadVariableNode) n).getVariableName().equals("this") | usesArgument(d, (ReadVariableNode) n)){
                        return true;

                    }

                }
            }

        }
        return false;
    }


    public boolean usesArgument(DeclareFunctionNode d, ReadVariableNode n)
    {
        for(String name : d.getFunction().getParameterNames())
        {
            if(n.getVariableName().equals(name)){
                return true;
            }

        }
        return false;
    }

    public void nestedCallback(ReadVariableNode n)
    {
        if(nested_callbacks.size()>2) {
            nestedCallbackNodes.add(n);
            nested_callbacks.clear();
        }
        if(n!=null) {
            if (n.getBlock().getFirstNode() instanceof ReadVariableNode && n.getBlock().getSuccessors().size() == 1 && n.getBlock().getSingleSuccessor().getFirstNode() instanceof CallNode) {
                for (AbstractNode a : n.getBlock().getNodes()) {
                    if (a instanceof DeclareFunctionNode) {
                        nested_callbacks.add(((DeclareFunctionNode) a).getFunction());
                        nestedCallback(findRead((DeclareFunctionNode) a));
                    }
                }
            }
        }
        nested_callbacks.clear();
    }

    public ReadVariableNode findRead(DeclareFunctionNode d)
    {
        for(BasicBlock b: d.getFunction().getBlocks())
        {
            for(AbstractNode n: b.getNodes())
            {
                if(n instanceof ReadVariableNode && n.getBlock().getSuccessors().size() == 1 && n.getBlock().getSingleSuccessor().getFirstNode() instanceof  CallNode){
                    return (ReadVariableNode) n;
                }
            }
        }
        return null;
    }

    @Override
    public void visitCatch(CatchNode c) {

    }

    public int globalVariableCount() {
        int count = 0;
        for (Function f : FlowGraph.getFunctions())
            for (AbstractNode n : f.globalFunctionVariables) {
                count++;
            }
        return count;
    }

    public String reportSwitchStatements() {
        String msg = "********Complex Switch********\r\n";
        String output = "";
        int count = 0;
        for (IfNode n: switchNodes) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Switch statement");
            output += "Instance at line: " + n.getSourceLocation().getLineNumber() + "\r\n";
            count++;
        }
        msg += "Number of occurences: " + count + "\r\n";
        msg += output;
        return msg;
    }

    public String reportNestedCallbacks() {
        String msg = "********Nested Callbacks********\r\n";
        String output = "";
        int count = 0;
        for (ReadVariableNode n: nestedCallbackNodes) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Nested Callback");
            output += "Instance at line: " + n.getSourceLocation().getLineNumber() + "\r\n";
            count++;
        }
        msg += "Number of occurences: " + count + "\r\n";
        msg += output;
        return msg;
    }

    public String reportExtraBinds() {
        String msg = "********Extra Bind********\r\n";
        String output = "";
        int count = 0;
        for (ReadPropertyNode n: extraBindNodes) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Extra Bind");
            output += "Instance at line: " + n.getSourceLocation().getLineNumber() + "\r\n";
            count++;
        }
        msg += "Number of occurences: " + count + "\r\n";
        msg += output;
        return msg;
    }

    public String reportLongParameterLists() {
        String msg = "********Long Parameter List********\r\n";
        String output = "";
        int count = 0;
        for (DeclareFunctionNode n: longParameterList) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Long Parameter List");
            output += "Instance at line: " + n.getSourceLocation().getLineNumber() + "\r\n";
            count++;
        }
        msg += "Number of occurences: " + count + "\r\n";
        msg += output;
        return msg;
    }

    public String reportConditionalAssignments() {
        String msg = "********Assignment in Conditionals********\r\n";
        String output = "";
        int count = 0;
        for (IfNode n: conditionalAssignments) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Assignment in Conditioinal Statement");
            output += "Instance at line: " + n.getSourceLocation().getLineNumber() + "\r\n";
            count++;
        }
        msg += "Number of occurences: " + count + "\r\n";
        msg += output;
        return msg;
    }

    public void reportGlobalVariables() {
        for (Function functions: FlowGraph.getFunctions())
            try {
            for (AbstractNode anode: functions.globalFunctionVariables) {
                    if (functions.functionsAsVariables.contains(getVariableName(anode))) {
                        functions.globalFunctionVariables.remove(anode);
                    }
                }
            } catch (ConcurrentModificationException cme) {System.out.println("Concurrent Modification Exception. Global variable report may be innacurate.");}
        if (globalVariableCount() > 0)
            for (Function f: FlowGraph.getFunctions())
                for (AbstractNode n: f.globalFunctionVariables) {
                    if (mainGlobalVariables.add(getVariableName(n))) {
                        String msg = "Global variable ";
                        if (f.loopVariablesString.contains(getVariableName(n)))
                            msg += "(loop variable) ";
                        addMessage(n, Status.CERTAIN, Severity.MEDIUM, msg + getVariableName(n));
                    }
                }
    }

    public String reportEmptyCatchNodes() {
        String msg = "********Empty Catch********\r\n";
        String output = "";
        int count = 0;
        for (CatchNode n: emptyCatchNodes) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Empty Catch Statement");
            output += "Instance at line: " + n.getSourceLocation().getLineNumber() + "\r\n";
            count++;
        }
        msg += "Number of occurences: " + count + "\r\n";
        msg += output;
        return msg;
    }

    public void reportUndeclaredVariable() {
        for (Function f: FlowGraph.getFunctions())
            for (AbstractNode n: f.undeclaredFunctionVariables){
                String msg = "Undeclared variable ";
                if (f.loopVariablesString.contains(getVariableName(n)))
                    msg += "(loop variable) ";
                addMessage(n, Status.CERTAIN, Severity.MEDIUM,msg + getVariableName(n));
            }
    }

    public void findCallDepth(CallNode n) {
        CallNode lastNode = n;
        Set<CallNode> currentCalls = newSet();
        BasicBlock firstBlock = n.getBlock();
        callNestCount = 0;
        BasicBlock secondBlock = firstBlock.getSingleSuccessor();
        try {
            while (!(secondBlock.getLastNode() instanceof ReturnNode) && (firstBlock.getLastNode() instanceof CallNode
                        || secondBlock.getLastNode() instanceof CallNode)) {
                if (secondBlock.getLastNode() instanceof CallNode) {
                    currentCalls.add((CallNode)secondBlock.getLastNode());
                    callNestCount++;
                    lastNode = ((CallNode)secondBlock.getLastNode());
                }
                firstBlock = secondBlock;
                secondBlock = secondBlock.getSingleSuccessor();
                if (callNestCount > 2)
                    if (n.isConstructorCall())
                        for (CallNode c: currentCalls)
                            constructorCalls.add(c);
                    else {
                        if (n.getSourceLocation().getLineNumber() == lastNode.getSourceLocation().getLineNumber()) {
                            nestedCalls.add(n);
                            for (CallNode cn: currentCalls)
                                subsequentCallNodes.add(cn);
                        }
                    }
            }
        }
        catch (AnalysisException ae) {}
    }

    public String reportChainedMessages() {
        String msg = "********Chained Message********\r\n";
        String output = "";
        int count = 0;
        for (AbstractNode n: nestedCalls) {
            addMessage(n, Status.CERTAIN, Severity.MEDIUM, "Chained message call");
            output += "Instance at line: " + n.getSourceLocation().getLineNumber() + "\r\n";
            count++;
        }
        msg += "Number of occurences: " + count + "\r\n";
        msg += output;
        return msg;
    }

    private void reportUnreachableFunctions() {
        for (Function f : functions) {
            if (!reachable_functions.contains(f))
                addMessage(f.getEntry().getFirstNode(), Status.CERTAIN, Severity.LOW, "Unreachable function" + (f.getName() != null ? " " + Strings.escape(f.getName()) : ""));
        }
    }

    private void reportUnreachableCode(FlowGraph fg) {
        for (Function f : fg.getFunctions()) {
            if (!reachable_functions.contains(f)) // do not report blocks inside functions that are unreachable themselves.
                continue;
            Set<BasicBlock> successors = newSet();
            Set<BasicBlock> successors_of_blocks_where_last_non_artificial_node_is_reachable = newSet();
            for (BasicBlock b : f.getBlocks()) {
                successors.addAll(b.getSuccessors());
                if (b.getExceptionHandler() != null)
                    successors.add(b.getExceptionHandler());
                AbstractNode lastNonArtificialNode = null;
                for (AbstractNode node : b.getNodes()) {
                    if (!node.isArtificial()) {
                        lastNonArtificialNode = node;
                    }
                }
                if (((lastNonArtificialNode == null && successors_of_blocks_where_last_non_artificial_node_is_reachable.contains(b)) || reachable_nodes.contains(lastNonArtificialNode)) &&
                        !(b.getLastNode() instanceof IfNode)) // exclude if nodes, those are reported separately if always true/false
                    successors_of_blocks_where_last_non_artificial_node_is_reachable.addAll(b.getSuccessors());
            }
            for (BasicBlock b : f.getBlocks()) {
                boolean prev_reachable = false;
                boolean isFirstNonArtificialNodeInBlock = true;
                for (AbstractNode n : b.getNodes()) {
                    if (n.getDuplicateOf() == null && !n.isArtificial() && !(n instanceof ReturnNode)) { // ignore duplicate nodes, artificial nodes, and return nodes
                        if (!reachable_nodes.contains(n)) {
                            final boolean shouldWarn;
                            if (isFirstNonArtificialNodeInBlock) {
                                shouldWarn = (n instanceof CatchNode || // unreachable catch block
                                        successors_of_blocks_where_last_non_artificial_node_is_reachable.contains(b) || // unreachable first node but predecessor block is reachable
                                        (!b.isEntry() && !successors.contains(b))); // block is neither function entry nor successor of another block
                            } else {
                                shouldWarn = prev_reachable;
                            }
                            if (shouldWarn) { // previous node in the block killed the flow
                                addMessage(n, Status.CERTAIN, Severity.LOW, "Unreachable code"); // see also "Unreachable function" and "The conditional expression is always true/false"
                                break; // no more messages for this block
                            }
                        }

                        prev_reachable = reachable_nodes.contains(n);
                    }
                    if (!n.isArtificial()) {
                        isFirstNonArtificialNodeInBlock = false;
                    }
                }
            }
        }
    }

    private void reportDeadAssignments() {
        Set<Pair<AbstractNode, String>> potentiallyDeadWrites = newSet();
        Set<Pair<AbstractNode, String>> undeadWrites = newSet();
        for (Entry<ObjectLabel, ObjReadsWrites> entry : obj_reads_writes.entrySet()) {
            ObjReadsWrites rw = entry.getValue();
            for (String s : rw.getProperties()) {
                // flag if definitely written and definitely not read (excluding 'length' and any-string properties)
                if (rw.getWriteStatus(s) == W_Status.WRITTEN) {
                    for (AbstractNode definiteWriteLocation : rw.getDefiniteWriteLocations(s)) {
                        if (rw.getReadStatus(s) == R_Status.NOT_READ) {
                            potentiallyDeadWrites.add(Pair.make(definiteWriteLocation, s));
                        } else {
                            undeadWrites.add(Pair.make(definiteWriteLocation, s));
                        }
                    }
                }
            }

            if (rw.isUnknownWritten() && !rw.isSomePropertyRead()) {
                for (AbstractNode n : rw.getDefaultWriteLocations()) {
                    String m_s = "Dead assignment, property is never read";
                    Message m = new Message(n, Status.CERTAIN, m_s, Severity.MEDIUM, true);
                    messages.put(m, m);
                }
            }
        }

        Set<Pair<AbstractNode, String>> deadWrites = newSet();
        deadWrites.addAll(potentiallyDeadWrites);
        deadWrites.removeAll(undeadWrites);
        for (Pair<AbstractNode, String> deadWrite : deadWrites) {
            String m_s = "Dead assignment, property " + deadWrite.getSecond() + " is never read";
            Message m = new Message(deadWrite.getFirst(), Status.CERTAIN, m_s, Severity.MEDIUM, true);
            messages.put(m, m);
        }
    }

    private void reportUnusedVariableOrParameter(FlowGraph fg) {
        for (Function f : fg.getFunctions()) {
            // Skip reporting unused variables and parameters for dead code.
            if (!reachable_functions.contains(f))
                continue;
            Set<String> names = newSet(f.getVariableNames());
            names.addAll(f.getParameterNames());
            Set<String> rv = read_variables.get(f);
            if (rv != null)
                names.removeAll(rv);
            for (String n : names) {
                AbstractNode declNode = getVarDeclNode(f, n);
                addMessage(declNode, Status.CERTAIN, Severity.LOW, "The variable " + Strings.escape(n) + " is never used");
            }
        }
    }

    private static AbstractNode getVarDeclNode(Function f, String n) {
        Collection<BasicBlock> blocks = f.getBlocks();
        if (f.getParameterNames().contains(n))
            return f.getEntry().getFirstNode();
        for (BasicBlock block : blocks) {
            List<AbstractNode> nodes = block.getNodes();
            for (AbstractNode node : nodes) {
                if (node instanceof DeclareVariableNode && ((DeclareVariableNode) node).getVariableName().equals(n)) {
                    return node;
                }
            }
        }
        throw new IllegalArgumentException("Variable " + n + " is not declared in this function!?!");
    }

    @Override
    public void setFlowgraph(FlowGraph fg) {
        flowgraph = fg;
    }

    /**
     * Add messages about shadowing. Shadowing occurs when a declared variable clashes either local functions or parameters.
     * This is a purely syntactic property, no analysis results are used.
     */
    public void reportShadowing(FlowGraph fg) { // FIXME: variable declarations cannot shadow functions or parameters (see 10.1.3 and micro/test181.js) - but the programmer may think so
        for (Function f : fg.getFunctions()) {
            Map<String, DeclareFunctionNode> declared_functions = newMap();
            Map<String, DeclareVariableNode> declared_variables = newMap();
            for (AbstractNode n : f.getEntry().getNodes()) {
                if (n instanceof DeclareFunctionNode) {
                    DeclareFunctionNode node = (DeclareFunctionNode) n;
                    if (node.getFunction().getName() != null) {
                        declared_functions.put(node.getFunction().getName(), node);
                    }
                }
                if (n instanceof DeclareVariableNode) {
                    DeclareVariableNode node = (DeclareVariableNode) n;
                    declared_variables.put(node.getVariableName(), node);
                }
            }
            for (DeclareFunctionNode n : declared_functions.values()) {
                String function_name = n.getFunction().getName();
                if (declared_variables.containsKey(function_name)) {
                    DeclareVariableNode node = declared_variables.get(function_name);
                    addMessage(node, Status.CERTAIN, Severity.LOW, "The variable declaration " + Strings.escape(node.getVariableName()) + " shadows a function");
                }
            }
            for (DeclareVariableNode n : declared_variables.values()) {
                String var_name = n.getVariableName();
                if (f.getParameterNames().contains(var_name)) {
                    DeclareVariableNode node = declared_variables.get(var_name);
                    addMessage(node, Status.CERTAIN, Severity.LOW, "The variable declaration " + Strings.escape(node.getVariableName()) + " shadows a parameter");
                }
            }
        }
    }

    private void visitBeginScanPhase() {
        for (Function functions: flowgraph.getFunctions())
        messages = newMap();
        scan_phase = true;
        for (Function f : flowgraph.getFunctions())
            for (BasicBlock b : f.getBlocks())
                for (AbstractNode n : b.getNodes())
                    n.visitBy((n1) -> n1.visitBy(new NodeVisitor() {

                        @Override
                        public void visit(NopNode n) {
                        }

                        @Override
                        public void visit(DeclareVariableNode n) {
                            Function f = n.getBlock().getFunction();
                            if (f.declaredVariableStrings.add(getVariableName(n))) {
                                f.declaredFunctionVariables.add(n);
                            }
                            if (n.getBlock().getFunction().isMain()) {
                                n.getBlock().getFunction().globalFunctionVariables.add(n);
                            }
                        }

                        @Override
                        public void visit(ConstantNode n) {
                        }

                        @Override
                        public void visit(NewObjectNode n) {
                        }

                        @Override
                        public void visit(UnaryOperatorNode n) {
                        }

                        @Override
                        public void visit(BinaryOperatorNode n) {
                        }

                        @Override
                        public void visit(ReadVariableNode n) {
                            nested_callbacks.clear();
                            nestedCallback(n);
                            findMessageDepth(n);
                            if (!n.getVariableName().equals("this")) {
                                read_variable_nodes++;
                            }
                        }

                        @Override
                        public void visit(WriteVariableNode n) {
                            Function f = n.getBlock().getFunction();
                            for (AbstractNode anode: n.getBlock().getNodes())
                                if (anode instanceof DeclareFunctionNode)
                                    if (((DeclareFunctionNode) anode).getResultRegister() == n.getValueRegister()) {
                                        f.functionsAsVariables.add(n.getVariableName());
                                    }
                            if (n.getVariableName() != "window")
                                if (!f.getVariableNames().contains(n.getVariableName()) && !f.getParameterNames().contains(n.getVariableName())) {
                                    if (f.undeclaredVarStrings.add(getVariableName(n)))
                                        f.undeclaredFunctionVariables.add(n);
                                    if (f.globalVarStrings.add(getVariableName(n)))
                                        f.globalFunctionVariables.add(n);
                            }
                        }

                        @Override
                        public void visit(ReadPropertyNode n) {
                            if(extraBind(n)) {
                                extraBindNodes.add(n);
                            }
                            property_access_nodes++;
                            if (n.isPropertyFixed()) {
                                read_fixed_property_nodes++;
                            }
                        }

                        @Override
                        public void visit(WritePropertyNode n) {
                            property_access_nodes++;
                            Function f = n.getBlock().getFunction();
                            for (AbstractNode anode: n.getBlock().getNodes())
                                if (anode instanceof DeclareFunctionNode)
                                    if (((DeclareFunctionNode) anode).getResultRegister() == n.getValueRegister()) {
                                        try {
                                            f.functionsAsVariables.add(getVariableName(n));
                                        } catch (NullPointerException npe) {}
                                    }
                            for (AbstractNode anode: n.getBlock().getNodes()) {
                                if (anode instanceof ReadVariableNode)
                                    if (((ReadVariableNode) anode).getResultRegister() == n.getBaseRegister())
                                        if (((ReadVariableNode) anode).getVariableName() == "window" || ((ReadVariableNode) anode).getVariableName()
                                                == "this" && f.isMain()) {
                                            f.globalFunctionVariables.add(n);
                                            if (!f.getVariableNames().contains(n.getPropertyString()))
                                                f.undeclaredFunctionVariables.add(n);
                                        }
                            }
                        }

                        @Override
                        public void visit(DeletePropertyNode n) {
                            if (!n.isVariable()) {
                                property_access_nodes++;
                            }
                        }

                        @Override
                        public void visit(TypeofNode n) {
                        }

                        @Override
                        public void visit(IfNode n) {
                            //System.out.println("Block: " + n.getBlock().getIndex() + " has converging node of " + findConvergentBlock(n).getIndex());
                            if (findSwitch(n)){
                                switchNodes.add(n);
                            }
                            else {
                                depthCount = 0;
                                observedBlocks.clear();
                                beginFindDepth(n.getBlock());
                                if (depthCount > 3)
                                    nestedIfs.add(n);
                                visitedBlocks.clear();
                                if (searchSucc(n.getBlock())) {
                                    loopBlocks.add(n.getBlock());
                                    if (n.getBlock().getFirstNode() instanceof ReadVariableNode) {
                                        f.loopVariables.add(((ReadVariableNode) n.getBlock().getFirstNode()));
                                        f.loopVariablesString.add(((ReadVariableNode) n.getBlock().getFirstNode()).getVariableName());
                                    }
                                }
                            }
                        }

                        @Override
                        public void visit(DeclareFunctionNode n) {
                            Function f = n.getFunction();
                            int count = 0;
                            if (f.getSource().length() > 0)
                                for(int i =0; i < f.getSource().length(); ++i)
                                {
                                    if (f.getSource().charAt(i) == '\n') {
                                        if(f.getSource().charAt(i+1) != '\n') {
                                            ++count;
                                        }
                                    }
                                }
                            if (count > 50)
                                longMethods.add(n);
                        }

                        @Override
                        public void visit(CallNode n) {
                            call_nodes++;
                            //parArgMismatch(n);
                            //if (!(constructorCalls.contains(n)) && !subsequentCallNodes.contains(n))
                                //findCallDepth(n);
                        }

                        @Override
                        public void visit(ReturnNode n) {
                        }

                        @Override
                        public void visit(ExceptionalReturnNode n) {
                        }

                        @Override
                        public void visit(ThrowNode n) {
                        }

                        @Override
                        public void visit(CatchNode n) {
                            if (n.getBlock().getSingleSuccessor().getFirstNode() instanceof EndWithNode)
                                emptyCatchNodes.add(n);

                        }

                        @Override
                        public void visit(BeginWithNode n) {
                        }

                        @Override
                        public void visit(EndWithNode n) {
                        }

                        @Override
                        public void visit(BeginForInNode n) {
                        }

                        @Override
                        public void visit(NextPropertyNode n) {
                        }

                        @Override
                        public void visit(HasNextPropertyNode n) {
                        }

                        @Override
                        public void visit(AssumeNode n) {
                        }

                        @Override
                        public void visit(EventDispatcherNode n) {
                        }

                        @Override
                        public void visit(EndForInNode n) {
                        }

                        @Override
                        public void visit(BeginLoopNode n) {

                        }

                        @Override
                        public void visit(EndLoopNode n) {

                        }
                    }));
    }

    private void visitEndScanPhase() {
        if (!Options.get().isNoMessages()) {
            reportUnreachableFunctions();
            reportUnreachableCode(flowgraph);
            reportUnusedVariableOrParameter(flowgraph);
            reportDeadAssignments();
            reportShadowing(flowgraph);
            reportGlobalVariables();
            results += reportLongMethods();
            results += reportLongParameterLists();
            results += reportExtraBinds();
            results += reportParameterArgumentMismatch();
            results += reportNestedCallbacks();
            results += reportNestedIfs();
            results += reportVariableNames();
            results += reportSwitchStatements();
            results += reportReassignedVariable();
            results += reportEmptyCatchNodes();
            results += reportConditionalAssignments();
            results += reportChainedMessages();
            reportAlreadyDeclaredVariables();
            outputResults(results);
            if (Options.get().isShowVariableInfoEnabled()) {
                type_collector.logTypeInformation();
            }
            // TODO: this de-duplication should happen somewhere else?
            Set<String> emittedOutput = newSet(); // avoid redundant output
            for (Message message : getSortedMessages()) {
                if (HostEnvSources.isHostEnvSource(message.getNode().getSourceLocation()) || emittedOutput.contains(message.toString())) {
                    continue;
                }
                message.emit();
                emittedOutput.add(message.toString());
            }
        }

        if (Options.get().isStatisticsEnabled()) {
            log.info(this.toString());
            log.info(callgraph.getCallGraphStatistics());
            log.info("BlockState: created=" + State.getNumberOfStatesCreated() + ", makeWritableStore=" + State.getNumberOfMakeWritableStoreCalls());
            log.info("Obj: created=" + Obj.getNumberOfObjsCreated() + ", makeWritableProperties=" + Obj.getNumberOfMakeWritablePropertiesCalls());
            log.info("Value cache: hits=" + Value.getNumberOfValueCacheHits() + ", misses=" + Value.getNumberOfValueCacheMisses() + ", finalSize=" + Value.getValueCacheSize());
            log.info("Value object set cache: hits=" + Value.getNumberOfObjectSetCacheHits() + ", misses=" + Value.getNumberOfObjectSetCacheMisses() + ", finalSize=" + Value.getObjectSetCacheSize());
            log.info("ScopeChain cache: hits=" + ScopeChain.getNumberOfCacheHits() + ", misses=" + ScopeChain.getNumberOfCacheMisses() + ", finalSize=" + ScopeChain.getCacheSize());
            log.info("Basic blocks: " + flowgraph.getNumberOfBlocks());
        }

        if (Options.get().isCoverageEnabled()) {
            logUnreachableMap();
        }

        if (Options.get().isCallGraphEnabled()) {
            log.info(callgraph.toString());
            File outdir = new File("out");
            if (!outdir.exists()) {
                outdir.mkdir();
            }
            String filename = "out" + File.separator + "callgraph.dot";
            try (FileWriter f = new FileWriter(filename)) {
                log.info("Writing call graph to " + filename);
                callgraph.toDot(new PrintWriter(f));
            } catch (IOException e) {
                log.error("Unable to write " + filename + ": " + e.getMessage());
            }
        }
    }

    public static void outputResults(String results) {
        try{
            FileWriter fstream = new FileWriter("SmellReport.txt", false);
            BufferedWriter out  = new BufferedWriter(fstream);
            out.write("********Excessive Global Variables********\r\n");
            out.write("Number of global variables: " + Monitoring.mainGlobalVariables.size() + "\r\n");
            for (String s: Monitoring.mainGlobalVariables)
                out.write(s + ", ");
            out.write("\r\n");
            out.write(results);

            out.close();
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }

    @Override
    public void visitNodeTransfer(AbstractNode n) {
        node_transfers++;
    }

    /**
     * Registers a block transfer occurrence.
     * Also measures memory usage if enabled.
     */
    @Override
    public void visitBlockTransfer(BasicBlock block, State state) {
        block_transfers++;
        if (Options.get().isMemoryMeasurementEnabled()) {
            System.gc();
            long m = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
            if (m > max_memory) {
                max_memory = m;
            }
        }
    }

    @Override
    public void visitUnknownValueResolve(boolean partial, boolean scanning) {
        if (scanning) {
            if (partial)
                unknown_value_resolve_scanning_partial++;
            else
                unknown_value_resolve_scanning_full++;
        } else {
            if (partial)
                unknown_value_resolve_analyzing_partial++;
            else
                unknown_value_resolve_analyzing_full++;
        }
    }

    @Override
    public void visitJoin() {
        joins++;
    }

    @Override
    public void visitNewFlow(BasicBlock b, Context c, State s, String diff, String info) {
        if (Options.get().isNewFlowEnabled() && b.isEntry()) {
            if (diff != null) {
                Map<Context, List<String>> m = newflows.get(b);
                if (m == null) {
                    m = newMap();
                    newflows.put(b, m);
                }
                addToMapList(m, c, diff);
            }
//			if (info != null) {
//				try {
//					File outdir = new File("out" + File.separator + "newflows"); // TODO: separate files for separate contexts?
//					if (!outdir.exists()) {
//						outdir.mkdirs();
//					}
//					try (FileWriter fw = new FileWriter("out" + File.separator + "newflows" + File.separator + "line" + b.getFunction().getSourceLocation().getLineNumber() + "-" +
//							(next_newflow_file++) + "-" + info + ".dot")) {
//						fw.write(s.toDot());
//					}
//				} catch (IOException e) {
//					throw new AnalysisException(e);
//				}
//			}

        }
//					try (FileWriter fw = new FileWriter("out" + File.separator + "newflows" + File.separator + "line" + b.getFunction().getSourceLocation().getLineNumber() + "-" +
//							(next_newflow_file++) + "-" + info + ".dot")) {
//						fw.write(s.toDot());
//					}
//				} catch (IOException e) {
//					throw new AnalysisException(e);
//				}
//			}
//		}
    }

    /**
     * Registers the function and checks whether it is unreachable.
     */
    @Override
    public void visitFunction(Function f, Collection<State> entry_states) {
        functions.add(f);
        for (State s : entry_states) {
            if (!s.isNone()) {
                reachable_functions.add(f); // see also "Unreachable code" and "The conditional expression is always true/false"
                break;
            }
        }
    }

    @Override
    public void visitFunction(Function f){
        parameterNum = f.getParameterNames().size();
        if(f.getParameterNames().size() >= 5)
            longParameterList.add(f.getNode());
    }

    @Override
    public void visitReachableNode(AbstractNode n) {
        AbstractNode d = n.getDuplicateOf();
        if (d != null)
            n = d;
        reachable_nodes.add(n);
    }

    /**
     * Checks whether an absent variable is read.
     *
     * @param n (non-this) read variable operation
     * @param v the value being read
     */
    @Override
    public void visitReadNonThisVariable(ReadVariableNode n, Value v) {
        if (!scan_phase) {
            return;
        }
        Status s;
        if (v.isMaybeAbsent() && !v.isMaybePresent()) {
            s = Status.CERTAIN;
        } else if (v.isMaybeAbsent()) {
            s = Status.MAYBE;
        } else {
            s = Status.NONE;
        }
        if (s != Status.NONE) {
            absent_variable_read.add(n);
        }
        addMessage(n, s, Severity.HIGH, "ReferenceError, reading absent variable " + Strings.escape(n.getVariableName()));
    }

    /**
     * Checks whether the read of 'this' yields the global object.
     *
     * @param n (this) read variable operation
     * @param v the value being read
     */
    @Override
    public void visitReadThis(ReadVariableNode n, Value v, State state, ObjectLabel global_obj) {
        if (!scan_phase) {
            return;
        }
        v = UnknownValueResolver.getRealValue(v, state);
        Status s;
        if (v.getObjectLabels().contains(global_obj)) {
            if (v.getObjectLabels().size() == 1 && !v.isMaybePrimitive()) {
                s = Status.CERTAIN;
            } else {
                s = Status.MAYBE;
            }
        } else {
            s = Status.NONE;
        }
        addMessage(n, s, Severity.MEDIUM, "Reading 'this' yields the global object");
        if (v.getObjectLabels().size() > 1) {
            addMessage(n, Status.INFO, Severity.LOW,
                    "'this' refers to multiple abstract objects, which may cause loss of precision"); // ...but still sound!
            if (log.isDebugEnabled())
                log.debug("this = " + v);
        } else if (v.getObjectLabels().size() == 1 && !v.getObjectLabels().iterator().next().isSingleton() && !Options.get().isRecencyDisabled()) {
            addMessage(n, Status.INFO, Severity.LOW,
                    "'this' refers to a summary abstract object, which may cause loss of precision"); // ...but still sound!
            if (log.isDebugEnabled())
                log.debug("this = " + v);
        }
    }

    /**
     * Checks whether the variable read yields null/undefined.
     * Variables named 'undefined' are ignored.
     *
     * @param n read variable operation
     * @param v the value being read
     */
    @Override
    public void visitReadVariable(ReadVariableNode n, Value v, State state) {
        if (!scan_phase) {
            return;
        }
        String varname = n.getVariableName();
        if (varname.equals("undefined")) {
            return;
        }
        v = UnknownValueResolver.getRealValue(v, state);
        Status s;
        if (v.isNullOrUndef()) {
            s = Status.CERTAIN;
        } else if (v.isMaybeNull() || v.isMaybeUndef()) {
            s = Status.MAYBE;
        } else {
            s = Status.NONE;
        }
        addMessage(n, s, Severity.MEDIUM_IF_CERTAIN_NONE_OTHERWISE, "Variable " + Strings.escape(varname) + " is null/undefined");
    }

    /**
     * Checks whether the branch condition is always true or always false.
     *
     * @param n if node
     * @param v the boolean value
     */
    @Override
    public void visitIf(IfNode n, Value v) { // see also "Unreachable code" and "Unreachable function"
        if (!scan_phase || n.isArtificial()) {
            return;
        }
        try{
            if((n.getBlock().getNodes().get(n.getBlock().getNodes().size() -2) instanceof WriteVariableNode)) {
                conditionalAssignments.add(n);
            }
        }
        catch (ArrayIndexOutOfBoundsException aiobe){}
        boolean is_maybe_true = v.isMaybeTrue();
        boolean is_maybe_false = v.isMaybeFalse();
        addMessage(n, is_maybe_true ? (is_maybe_false ? Status.MAYBE : Status.CERTAIN) : Status.NONE,
                Severity.MEDIUM_IF_CERTAIN_NONE_OTHERWISE, "The conditional expression is always true");
        addMessage(n, is_maybe_false ? (is_maybe_true ? Status.MAYBE : Status.CERTAIN) : Status.NONE,
                Severity.MEDIUM_IF_CERTAIN_NONE_OTHERWISE, "The conditional expression is always false");
    }

    /**
     * Checks whether the 'instanceof' operation may fail.
     *
     * @param n                               node performing the operation
     * @param maybe_v2_non_function           set if the second parameter may be a non-function value
     * @param maybe_v2_function               set if the second parameter may be a function value
     * @param maybe_v2_prototype_primitive    set if the prototype property of the second parameter may be a primitive value
     * @param maybe_v2_prototype_nonprimitive set if the prototype property of the second parameter may be an object value
     */
    @Override
    public void visitInstanceof(AbstractNode n,
                                boolean maybe_v2_non_function, boolean maybe_v2_function,
                                boolean maybe_v2_prototype_primitive, boolean maybe_v2_prototype_nonprimitive) {
        if (!scan_phase) {
            return;
        }
        Status s1;
        if (maybe_v2_non_function) {
            if (!maybe_v2_function) {
                s1 = Status.CERTAIN;
            } else {
                s1 = Status.MAYBE;
            }
        } else {
            s1 = Status.NONE;
        }
        addMessage(n, s1, Severity.HIGH, "TypeError, non-function object at 'instanceof'");
        Status s2;
        if (maybe_v2_prototype_primitive) {
            if (!maybe_v2_prototype_nonprimitive) {
                s2 = Status.CERTAIN;
            } else {
                s2 = Status.MAYBE;
            }
        } else {
            s2 = Status.NONE;
        }
        addMessage(n, s2, Severity.HIGH, "TypeError, non-object prototype at 'instanceof'");
    }

    /**
     * Checks whether the 'in' operation may fail.
     *
     * @param n                  node performing the operation
     * @param maybe_v2_object    if the second parameter may be an object value
     * @param maybe_v2_nonobject if the second parameter may be a non-object value
     */
    @Override
    public void visitIn(AbstractNode n, boolean maybe_v2_object, boolean maybe_v2_nonobject) {
        if (!scan_phase) {
            return;
        }
        Status s;
        if (maybe_v2_nonobject) {
            if (!maybe_v2_object) {
                s = Status.CERTAIN;
            } else {
                s = Status.MAYBE;
            }
        } else {
            s = Status.NONE;
        }
        addMessage(n, s, Severity.HIGH, "TypeError, non-object at 'in'");
    }

    /**
     * Checks whether the property access operation may dereference null or undefined.
     *
     * @param n       operation that accesses a property
     * @param baseval base value for the access
     */
    @Override
    public void visitPropertyAccess(Node n, Value baseval) {
        if (!scan_phase) {
            return;
        }
        Status s;
        if (baseval.isNullOrUndef()) {
            s = Status.CERTAIN;
        } else if (baseval.isMaybeNull() || baseval.isMaybeUndef()) {
            s = Status.MAYBE;
        } else {
            s = Status.NONE;
        }
        if (s != Status.NONE) {
            null_undef_base.add(n);
        }
        addMessage(n, s, Severity.HIGH, "TypeError, accessing property of null/undefined");
    }

    /**
     * Checks whether the property read operation accesses an absent property and whether the operation returns null/undefined.
     *
     * @param n           read property operation
     * @param objlabels   objects being read from
     * @param propertystr description of the property name
     * @param maybe       if there may be more than one value
     * @param state       current abstract state
     * @param v           property value with attributes
     */
    @Override
    public void visitReadProperty(ReadPropertyNode n, Set<ObjectLabel> objlabels, Str propertystr, boolean maybe, State state, Value v) {
        if (!scan_phase) {
            throw new AnalysisException("Should only be invoked in scan phase");
        }
        Status s;
        if (!maybe && v.isMaybeAbsent() && !v.isMaybePresent()) {
            s = Status.CERTAIN;
        } else if (v.isMaybeAbsent()) {
            s = Status.MAYBE;
        } else {
            s = Status.NONE;
        }
        if (s != Status.NONE && n.isPropertyFixed()) {
            absent_fixed_property_read.add(n);
        }
        if (n.isPropertyFixed()) {
            addMessage(n, s, Severity.MEDIUM, "Reading absent property " + n.getPropertyString());
        } else {
            addMessage(n, s, Severity.LOW, "Reading absent property (computed name)");
        }
        Status s2;
        v = UnknownValueResolver.getRealValue(v, state);
        if (v.isNullOrUndef() && s != Status.CERTAIN) {
            s2 = Status.CERTAIN;
        } else if (v.isMaybeNull() || v.isMaybeUndef()) {
            s2 = Status.MAYBE;
        } else {
            s2 = Status.NONE;
        }
        addMessage(n, s2, Severity.MEDIUM_IF_CERTAIN_NONE_OTHERWISE, "Property is null/undefined");
    }

    /**
     * Warns about reads from unknown properties;
     * also registers a read operation on abstract objects.
     * Properties named 'length' on array objects are ignored.
     *
     * @param n             the node responsible for the read
     * @param objs          the objects being read from
     * @param propertystr   description of the property name
     * @param check_unknown if set, warn about reads from unknown properties
     */
    @Override
    public void visitPropertyRead(AbstractNode n, Set<ObjectLabel> objs, Str propertystr, State state, boolean check_unknown) {
        if (!scan_phase) {
            return;
        }
        // warn about potential loss of precision
        if (check_unknown && checkPropertyNameMayInterfereWithBuiltInProperties(propertystr)) {
            addMessage(n, Status.INFO, Severity.LOW,
                    "Reading from unknown property that may cause loss of precision"); // ...but still sound!
        }
        // register read operation on abstract object
        String propertyname = propertystr.getStr();
        if (propertyname != null && propertyname.equals("length")) {
            // Proceed if we find an object label that is *not* an array.
            boolean only_array_length = true;
            for (ObjectLabel ol : objs)
                if (ol.getKind() != Kind.ARRAY) {
                    only_array_length = false;
                    break;
                }
            if (only_array_length)
                return;
        }
        Set<ObjectLabel> os = newSet();
        // Only give warnings for objects created by the user (getNode != null) since reading and writing properties
        // related to the DOM might be desirable for side effects.
        for (ObjectLabel objlabel : objs) {
            // TODO: objlabel.isHostObject() exists, but does not do precisely the same thing. Figure out what the correct behavior is.
            if (objlabel.getNode() != null) {
                for (ObjectLabel oo : (propertyname == null ? state.getPrototypesUsedForUnknown(objlabel) : state.getPrototypeWithProperty(objlabel, propertyname))) { // TODO: this is also used for ReadVariableNode?
                    if (oo.getNode() != null) { // TODO: Only give warnings for user objects, others maybe DOM or similar with side effects
                        os.add(oo.makeSingleton());
                    }
                }
            }
        }
        for (ObjectLabel objlabel : os) {
            // Record reading of arguments[propertystr] as reading of the actual function arguments as well.
            if (objlabel.getKind() == Kind.ARGUMENTS) {
                Function f = n.getBlock().getFunction();
                List<String> args = f.getParameterNames();
                // Fall through if there are no arguments to the function or reading something
                // other than an array index.
                if (args == null || propertyname != null && !Strings.isArrayIndex(propertyname))
                    continue;
                String arg = null;
                if (propertyname != null && Integer.valueOf(propertyname) < args.size())
                    arg = args.get(Integer.valueOf(propertyname));
                // Add all arguments if we aren't sure which we read.
                if (arg == null)
                    addAllToMapSet(read_variables, f, args);
                else
                    addToMapSet(read_variables, f, arg);
            }
            ObjReadsWrites i = obj_reads_writes.get(objlabel);
            if (i == null) {
                i = new ObjReadsWrites();
                obj_reads_writes.put(objlabel, i);
            }
            if (propertyname == null) {
                i.readUnknown();
            } else if (os.size() == 1) {
                i.readDefinite(propertyname);
            } else {
                i.readMaybe(propertyname);
            }
        }
    }

    private static boolean checkPropertyNameMayInterfereWithBuiltInProperties(Str propertystr) {
        return !propertystr.isMaybeSingleStr() &&
                (propertystr.isMaybeStrIdentifier() || propertystr.isMaybeStrIdentifierParts() ||
                        propertystr.isMaybeStrPrefixedIdentifierParts() || propertystr.isMaybeStrJSON()); // TODO: more precise pattern of what may interfere?
    }

    /**
     * Warns about writes to unknown properties;
     * also registers a write operation on abstract objects.
     * Properties named 'length' on array objects are ignored.
     * Writes to the arguments object are also ignored.
     *
     * @param n           the node responsible for the write
     * @param objs        the objects being written to
     * @param propertystr description of the property name
     */
    @Override
    public void visitPropertyWrite(Node n, Set<ObjectLabel> objs, Str propertystr) {
        if (!scan_phase) {
            return;
        }
        // warn about potential loss of precision
        if (checkPropertyNameMayInterfereWithBuiltInProperties(propertystr)) {
            addMessage(n,
                    Status.INFO,
                    Severity.MEDIUM,
                    "Writing to unknown property that may cause loss of precision"); // ...but still sound!
        }
        // register write operation on abstract object
        String propertyname = propertystr.getStr();
        if (propertyname != null && propertyname.equals("length")) {
            // Proceed if we find an object label that is *not* an array.
            boolean only_array_length = true;
            for (ObjectLabel ol : objs)
                if (ol.getKind() != Kind.ARRAY) {
                    only_array_length = false;
                    break;
                }
            if (only_array_length)
                return;
        }
        Set<ObjectLabel> os = newSet();
        for (ObjectLabel o : objs) {
            // Local variables end up in activation record object labels.
            // We do not consider that a property write, so filter them out.
            if (o.getNode() != null && o.getKind() != Kind.ACTIVATION) {
                os.add(o.makeSingleton());
            }
        }
        for (ObjectLabel objlabel : os) {
            ObjReadsWrites i = obj_reads_writes.get(objlabel);
            if (i == null) {
                i = new ObjReadsWrites();
                obj_reads_writes.put(objlabel, i);
            }
            if (propertyname == null) {
                i.writeUnknown(n);
            } else if (objs.size() == 1) {
                i.writeDefinite(propertyname, n);
            } else {
                i.writeMaybe(propertyname);
            }
        }
    }

    /**
     * Registers the name, location, and value of a variable being read or written.
     */
    @Override
    public void visitVariableOrProperty(String var, SourceLocation loc, Value value, Context context, State state) {
        if (scan_phase && Options.get().isShowVariableInfoEnabled()) {
            type_collector.record(var, loc, UnknownValueResolver.getRealValue(value, state), context);
        }
    }

    @Override
    public void visitNativeFunctionReturn(AbstractNode node, HostObject hostObject, Value result) {
        // ignore
    }

    /**
     * Checks whether the function is invoked both as a constructor (with 'new') and as a function/method (without 'new').
     *
     * @param f           function being called
     * @param call        node responsible for the call
     * @param constructor if set, the call uses 'new'
     */
    @Override
    public void visitUserFunctionCall(Function f, AbstractNode call, boolean constructor) { // TODO: avoid warning if the call is a super-call in a constructor
        Status s;
        if (!scan_phase) {
            if (constructor) { // in non-scan phase, collect all constructor calls
                called_as_constructor.add(f);
            }
            return;
        } else if (!constructor && called_as_constructor.contains(f)) { // in scan phase, report non-constructor calls to functions that are also used in constructor calls
            s = Status.CERTAIN;
        } else
            s = Status.NONE;
        addMessage(call, // use the location of the non-constructor call node
                s,
                Severity.MEDIUM,
                "The function" + (f.getName() != null ? " " + Strings.escape(f.getName()) : "") + " is invoked both as constructor and function");
    }

    /**
     * Registers a potential call/construct to a non-function value.
     *
     * @param n                  node responsible for the call
     * @param maybe_non_function if set, this call may involve a non-function value
     * @param maybe_function     if set, this call may involve a function value
     */
    @Override
    public void visitCall(AbstractNode n, boolean maybe_non_function, boolean maybe_function) {
        if (!scan_phase) {
            return;
        }
        Status s = maybe_non_function ? (maybe_function ? Status.MAYBE : Status.CERTAIN) : Status.NONE;
        if (s != Status.NONE) {
            call_to_non_function.add(n);
        }
        addMessage(n, s, Severity.HIGH, "TypeError, call to non-function");
    }

    /**
     * Registers a call to eval.
     *
     * @param n node that may call eval
     * @param v value being eval'ed
     */
    @Override
    public void visitEvalCall(AbstractNode n, Value v) {
        if (!scan_phase || !Options.get().isEvalStatistics()) {
            return;
        }
        Value vv = eval_calls.get(n);
        if (vv != null) {
            v = v.join(vv);
        }
        eval_calls.put(n, v);
    }

    /**
     * Registers a write to innerHTML.
     *
     * @param n node where the write occurs
     * @param v value being written
     */
    @Override
    public void visitInnerHTMLWrite(Node n, Value v) {
        if (!scan_phase || !Options.get().isEvalStatistics()) {
            return;
        }
        Value vv = inner_html_writes.get(n);
        if (vv != null) {
            v = v.join(vv);
        }
        inner_html_writes.put(n, v);
    }

    /**
     * Checks the number of parameters for a call to a native function.
     *
     * @param n                   node responsible for the call
     * @param hostobject          the native function being called
     * @param num_actuals_unknown if set, the number of actuals is unknown
     * @param num_actuals         number of actuals (if num_actuals_unknown is not set)
     * @param min                 minimum number of parameters expected
     * @param max                 maximum number of paramaters expected (-1 for any number)
     */
    @Override
    public void visitNativeFunctionCall(AbstractNode n, HostObject hostobject, boolean num_actuals_unknown, int num_actuals, int min, int max) {
        if (!scan_phase) {
            return;
        }
        Status s1 = (!num_actuals_unknown && num_actuals < min) ? Status.CERTAIN : Status.NONE;
        addMessage(n, s1, Severity.MEDIUM, "Too few parameters to function " + hostobject);
        if (max != -1) {
            Status s2 = num_actuals_unknown ? Status.MAYBE : num_actuals > max ? Status.CERTAIN : Status.NONE;
            addMessage(n, s2, Severity.HIGH, "Too many parameters to function " + hostobject);
        }
    }

    /**
     * Record type information about a var/prop read.
     */
    @Override
    public void visitRead(Node n, Value v, State state) {
        if (!scan_phase) {
            return;
        }
        v = UnknownValueResolver.getRealValue(v, state); // it is not important to preserve polymorphic values during the scan phase
        value_reads.put(new NodeAndContext<>(n, state.getContext()), v);
    }

    /**
     * Registers that the given variable is read; also checks for suspicious type mixings.
     *
     * @param n (non-this) read variable operation
     * @param v value being read
     */
    @Override
    public void visitVariableAsRead(ReadVariableNode n, Value v, State state) {
        if (!scan_phase) {
            return;
        }
        // record in read_variables
        String varname = n.getVariableName();
        Function f = n.getBlock().getFunction();
        // The arguments object is special, but other than that walk upwards in scope to find where the variable belongs.
        while (!"arguments".equals(varname) && !f.getVariableNames().contains(varname) && !f.getParameterNames().contains(varname)) {
            // Only main should be without an outer function.
            if (!f.hasOuterFunction())
                break;
            f = f.getOuterFunction(); // FIXME: what about 'with' and 'catch' blocks?
        }
        addToMapSet(read_variables, f, varname);
        // report suspicious type mixings
        v = UnknownValueResolver.getRealValue(v, state);
        Status s; // TODO: join values across contexts when checking for suspicious type mixings?
        int i = 0;
        if (!v.isNotStr()) {
            i++;
        }
        if (!v.isNotNum()) {
            i++;
        }
        if (!v.isNotBool()) {
            i++;
        }
        if (v.isMaybeObject() || v.isMaybeNull()) {
            i++;
        }
        if (i > 1) {
            s = Status.MAYBE;
        } else {
            s = Status.NONE;
        }
        addMessage(n, s, Severity.LOW, "The variable " + Strings.escape(varname) + " has values with different types"); // TODO: also check property reads with different types?
    }

    @Override
    public void visitRecoveryGraph(int size) {
        Integer count = recovery_graph_sizes.get(size);
        if (count == null)
            count = 0;
        recovery_graph_sizes.put(size, count + 1);
    }

    /**
     * Returns a string description of the results.
     */
    @Override
    public String toString() {
        NumberFormat formatter = NumberFormat.getNumberInstance(Locale.US);
        StringBuilder b = new StringBuilder();

        if (Options.get().isNewFlowEnabled()) {
            TreeMap<Integer, String> sorted = new TreeMap<>();
            b.append("\nNew flow at each function for each context:");
            for (Entry<BasicBlock, Map<Context, List<String>>> me1 : newflows.entrySet()) {
                Function f = me1.getKey().getFunction();
                b.append("\n").append(f).append(" at ").append(f.getSourceLocation()).append(":");
                for (Entry<Context, List<String>> me2 : me1.getValue().entrySet()) {
                    b.append("\n  ").append(me2.getKey()).append(" state diffs: ").append(me2.getValue().size());
                    for (String diff : me2.getValue()) {
                        if (diff != null) {
                            b.append("\n    state diff:").append(diff);
                        }
                    }
                    sorted.put(me2.getValue().size(), me1.getKey().getFunction() + " " + me1.getKey().getFunction().getSourceLocation() + ", context " + me2.getKey());
                }
            }
            b.append("\nSorted new flow:");
            for (Entry<Integer, String> me : sorted.entrySet())
                b.append("\n").append(me.getKey()).append(" new flows at ").append(me.getValue());
        }

        b.append("\n\nCall/construct nodes with potential call to non-function:                     ").append(call_to_non_function.size());
        b.append("\nTotal number of call/construct nodes:                                         ").append(call_nodes);
        b.append("\n==> Call/construct nodes that are certain to never call non-functions:        ").append(call_nodes > 0 ? ((call_nodes - call_to_non_function.size()) * 1000 / call_nodes) / 10f + "%" : "-");

        b.append("\n\nRead variable nodes with potential absent variable:                           ").append(absent_variable_read.size());
        b.append("\nTotal number of (non-this) read variable nodes:                               ").append(read_variable_nodes);
        b.append("\n==> Read variable nodes that are certain to never read absent variables:      ").append(read_variable_nodes > 0 ? ((read_variable_nodes - absent_variable_read.size()) * 1000 / read_variable_nodes) / 10f + "%" : "-");

        b.append("\n\nProperty access nodes with potential null/undef base:                         ").append(null_undef_base.size());
        b.append("\nTotal number of property access nodes:                                        ").append(property_access_nodes);
        b.append("\n==> Property access nodes that are certain to never have null/undef base:     ").append(property_access_nodes > 0 ? ((property_access_nodes - null_undef_base.size()) * 1000 / property_access_nodes) / 10f + "%" : "-");

        b.append("\n\nProperty reads resulting in singleton types:                                  ").append(getSingletonPropertyReads());
        b.append("\nVariable reads resulting in singleton types:                                  ").append(getSingletonVariableReads());
        // FIXME: only compare with reads with typeSize>0 ? (typeSize is 0 for polymorphic values...)
        float p_var = getVarReadsSize() > 0 ? (float) getSingletonVariableReads() * 100 / getVarReadsSize() : -1;
        float p_prop = getPropReadsSize() > 0 ? (float) getSingletonPropertyReads() * 100 / getPropReadsSize() : -1;
        float p_all = !value_reads.isEmpty() ? (float) (getSingletonPropertyReads() + getSingletonVariableReads()) * 100 / value_reads.size() : -1;
        b.append("\n==> Variable reads with singleton results:                                    ").append(p_var == -1 ? "-" : p_var + "%");
        b.append("\n==> Property reads with singleton results:                                    ").append(p_prop == -1 ? "-" : p_prop + "%");
        b.append("\n==> Reads with singleton results:                                             ").append(p_all == -1 ? "-" : p_all + "%");

        b.append("\n==> Average type size in property reads:                                      ").append(formatter.format(getAveragePropertyTypeSize()));
        b.append("\n==> Average type size in variable reads:                                      ").append(formatter.format(getAverageVariableTypeSize()));
        b.append("\n==> Average type size in all reads:                                           ").append(formatter.format(geTotalAverageTypeSize()));
        b.append("\n==> Reads with at most one type:                                              ").append(formatter.format(getReadsWithAtMostOneType()));
        b.append("\n==> Reads with at least two types:                                            ").append(formatter.format(getReadsWithAtleastTwoTypes()));

        b.append("\n\nFixed-property read nodes with potential absent property:                     ").append(absent_fixed_property_read.size());
        b.append("\nTotal number of fixed-property read nodes:                                    ").append(read_fixed_property_nodes);
        b.append("\n==> Fixed-property read nodes that are certain to never have absent property: ").append(read_fixed_property_nodes > 0 ? ((read_fixed_property_nodes - absent_fixed_property_read.size()) * 1000 / read_fixed_property_nodes) / 10f + "%" : "-");

        b.append("\n\nTotal number of functions:                                                    ").append(functions.size());
        b.append("\nNumber of unreachable functions:                                              ").append(functions.size() - reachable_functions.size());

        b.append("\n\nNode transfers: ").append(node_transfers);
        b.append("\nBlock transfers: ").append(block_transfers);
        b.append("\nUnknown-value recoveries: \n" + " analysis: partial=").append(unknown_value_resolve_analyzing_partial).append(", full=").append(unknown_value_resolve_analyzing_full).append("\n").append(" scanning: partial=").append(unknown_value_resolve_scanning_partial).append(", full=").append(unknown_value_resolve_scanning_full);
        b.append("\nState joins: ").append(joins).append("\n");

        if (Options.get().isMemoryMeasurementEnabled()) {
            formatter.setMaximumFractionDigits(2);
            b.append(" Max memory used: ").append(formatter.format((max_memory / (1024L * 1024L)))).append("M\n");
        }
        if (Options.get().isEvalStatistics()) {
            Set<String> eval_const_use = newSet();
            Set<String> inner_const_use = newSet();
            Map<AbstractNode, String> eval_anystr_use = newMap();
            Map<AbstractNode, String> inner_anystr_use = newMap();
            sortMustFromMaybe(eval_const_use, eval_anystr_use, eval_calls);
            sortMustFromMaybe(inner_const_use, inner_anystr_use, inner_html_writes);
            b.append("\nUse of eval/innerHTML\n");
            b.append(" Constant eval'ed strings:\n");
            for (String s : eval_const_use) {
                b.append("  ").append(s).append("\n").append("  ==\n");
            }
            b.append(" Constant innerHTML strings:\n");
            for (String s : inner_const_use) {
                b.append("  ").append(s).append("\n").append("  ==\n");
            }
            b.append(" Source locations with maybe values for eval:\n");
            for (Entry<AbstractNode, String> g : eval_anystr_use.entrySet()) {
                b.append("   ").append(g.getKey().getSourceLocation()).append(": ").append(g.getValue());
            }
            b.append("\n Source locations with maybe values for innerHTML:\n");
            for (Entry<AbstractNode, String> g : inner_anystr_use.entrySet()) {
                b.append("   ").append(g.getKey().getSourceLocation()).append(": ").append(g.getValue());
            }
            b.append("\n");
        }
        b.append("Recovery graph sizes: ").append(recovery_graph_sizes).append("\n");
        return b.toString();
    }

    private int getVarReadsSize() {
        int res = 0;
        for (NodeAndContext<Context> n : value_reads.keySet()) {
            if (n.getNode() instanceof ReadVariableNode) {
                res++;
            }
        }
        return res;
    }

    private int getPropReadsSize() {
        int res = 0;
        for (NodeAndContext<Context> n : value_reads.keySet()) {
            if (n.getNode() instanceof ReadPropertyNode) {
                res++;
            }
        }
        return res;
    }

    private double getAverageVariableTypeSize() {
        double res = 0;
        int div = 0;
        for (NodeAndContext<Context> n : value_reads.keySet()) {
            if (n.getNode() instanceof ReadVariableNode) {
                res += value_reads.get(n).typeSize();
                div++;
            }
        }
        if (div == 0) {
            return 0;
        }
        res = (1000 * res) / div;
        return res / 1000;
    }

    private double getAveragePropertyTypeSize() {
        double res = 0;
        int div = 0;
        for (NodeAndContext<Context> n : value_reads.keySet()) {
            if (n.getNode() instanceof ReadPropertyNode) {
                res += value_reads.get(n).typeSize();
                div++;
            }
        }
        if (div == 0) {
            return 0;
        }
        res = (1000 * res) / div;
        return res / 1000;
    }

    private double geTotalAverageTypeSize() {
        double res = 0;
        for (NodeAndContext<Context> n : value_reads.keySet()) {
            res += value_reads.get(n).typeSize();
        }
        res = (1000 * res) / value_reads.size();
        return res / 1000;
    }

    private int getReadsWithAtMostOneType() {
        int res = 0;
        for (NodeAndContext<Context> n : value_reads.keySet()) {
            if (value_reads.get(n).typeSize() <= 1) {
                res++;
            }
        }
        return res;
    }

    private int getReadsWithAtleastTwoTypes() {
        int res = 0;
        for (NodeAndContext<Context> n : value_reads.keySet()) {
            if (value_reads.get(n).typeSize() > 1) {
                res++;
            }
        }
        return res;
    }

    private int getSingletonPropertyReads() {
        int res = 0;
        for (NodeAndContext<Context> n : value_reads.keySet()) {
            if (n.getNode() instanceof ReadPropertyNode) {
                if (value_reads.get(n).typeSize() == 1)
                    res++;
            }
        }
        return res;
    }

    private int getSingletonVariableReads() {
        int res = 0;
        for (NodeAndContext<Context> n : value_reads.keySet()) {
            if (n.getNode() instanceof ReadVariableNode) {
                if (value_reads.get(n).typeSize() == 1)
                    res++;
            }
        }
        return res;
    }

    private static void sortMustFromMaybe(
            Set<String> eval_const_use,
            Map<AbstractNode, String> eval_anystr_use,
            Map<AbstractNode, Value> m) {
        for (Entry<AbstractNode, Value> e : m.entrySet()) {
            AbstractNode n = e.getKey();
            Value v = e.getValue();
            if (v.getStr() != null) {
                eval_const_use.add(v.getStr());
            } else {
                eval_anystr_use.put(n, v.toString());
            }
        }
    }

    /**
     * Produces output showing the parts of the code that is determined unreachable by the analysis.
     */
    private void logUnreachableMap() {
        for (String fs : unreachable_lines.keySet()) {
            log.info("== unreachable info for " + fs + " ==");
            try (BufferedReader r = new BufferedReader(new FileReader(fs))) {
                Set<Integer> ls = unreachable_lines.get(fs);
                if (ls == null) {
                    ls = Collections.emptySet();
                }
                String line;
                int i = 1;
                while ((line = r.readLine()) != null) {
                    String prefix;
                    if (ls.contains(i++)) {
                        prefix = "!!!";
                    } else
                        prefix = "   ";
                    log.info(prefix + line);
                }
            } catch (IOException e) {
                throw new AnalysisException(e);
            }
        }
    }

    /**
     * Adds a message for the given node. If not in scan phase, nothing is done.
     * Uses Status.INFO.
     * Uses the message as key (must be a fixed string).
     */
    @Override
    public void addMessageInfo(AbstractNode n, Severity severity, String msg) {
        addMessage(n, Status.INFO, severity, msg);
    }

    /**
     * Adds a message for the given node. If not in scan phase, nothing is done.
     * Uses Status.MAYBE.
     * Uses the message as key (must be a fixed string).
     */
    @Override
    public void addMessage(AbstractNode n, Severity severity, String msg) {
        addMessage(n, Status.MAYBE, severity, msg);
    }

    /**
     * Adds a message for the given node. If not in scan phase, nothing is done.
     * If the message already exists, the status is joined.
     * Uses the message as key (must be a fixed string).
     */
    private void addMessage(AbstractNode n, Status s, Severity severity, String msg) { // TODO: collect all message generation in Monitoring? (then make addMessage private?)
        addMessage(n, s, severity, msg, msg);
    }

    /**
     * Adds a message for the given node. If not in scan phase, nothing is done.
     * Uses Status.MAYBE.
     * The key must be a fixed string.
     */
    @Override
    public void addMessage(AbstractNode n, Severity severity, String key, String msg) {
        addMessage(n, Status.MAYBE, severity, key, msg);
    }

    /**
     * Adds a message for the given node. If not in scan phase, nothing is done.
     * If the message already exists, the status is joined.
     * The key must be a fixed string.
     */
    private void addMessage(AbstractNode n, Status s, Severity severity, String key, String msg) {
        if (scan_phase) {
            boolean dump;
            AbstractNode d = n.getDuplicateOf();
            if (d != null) // if n is a duplicate, use the original instead
                n = d;
            boolean ifGeneratedOrPseudoNode = n.getSourceLocation().getLocation() == null;
            Message m = new Message(n, s, key, msg, severity, ifGeneratedOrPseudoNode);
            Message mo = messages.get(m);
            if (mo != null) {
                Status old = mo.getStatus();
                mo.join(m);
                dump = old != mo.getStatus();
            } else {
                messages.put(m, m);
                dump = s != Status.NONE;
            }
            if (dump && log.isDebugEnabled()) {
                log.debug("addMessage: " + m.getStatus() + " " + m.getNode().getSourceLocation() + ": " + m.getMessage());
            }
        }
    }

    /**
     * Returns the collected messages.
     */
    @Override
    public Set<Message> getMessages() {
        return newSet(messages.values());
    }

    /**
     * Returns the sorted list of messages produced during scanning.
     * Ignores those messages that have Severity.MEDIUM_IF_CERTAIN_NONE_OTHERWISE if not Status.CERTAIN
     * and those that have Severity.LOW if not the option low-severity is enabled.
     */
    public List<Message> getSortedMessages() {
        List<Message> es = newList();
        for (Message m : messages.values()) {
            if (m.getStatus() != Status.NONE
                    && !(m.getSeverity() == Severity.MEDIUM_IF_CERTAIN_NONE_OTHERWISE && m.getStatus() != Status.CERTAIN)
                    && !(m.getSeverity() == Severity.LOW && !Options.get().isLowSeverityEnabled())) {
                es.add(m);
            }
        }
        Collections.sort(es);
        return es;
    }

    /**
     * Returns the collected type information.
     */
    @Override
    public Map<TypeCollector.VariableSummary, Value> getTypeInformation() {
        return type_collector.getTypeInformation();
    }

    @Override
    public boolean allowNextIteration() {
        return true;
    }

    @Override
    public void beginPhase(AnalysisPhase phase) {
        if (phase == AnalysisPhase.SCAN) {
            visitBeginScanPhase();
        }
    }

    @Override
    public void endPhase(AnalysisPhase phase) {
        if (phase == AnalysisPhase.SCAN) {
            visitEndScanPhase();
        }
    }

    @Override
    public void setCallGraph(CallGraph<State, Context, CallEdge> callgraph) {
        this.callgraph = callgraph;
    }

    @Override
    public void visitPostBlockTransfer(BasicBlock b, State state) {
        // ignore
    }
}
