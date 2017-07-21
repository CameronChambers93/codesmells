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

package dk.brics.tajs.analysis;

import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.flowgraph.Function;
import dk.brics.tajs.flowgraph.jsnodes.BeginForInNode;
import dk.brics.tajs.flowgraph.jsnodes.BeginLoopNode;
import dk.brics.tajs.flowgraph.jsnodes.EndLoopNode;
import dk.brics.tajs.lattice.Context;
import dk.brics.tajs.lattice.ContextArguments;
import dk.brics.tajs.lattice.HeapContext;
import dk.brics.tajs.lattice.ObjectLabel;
import dk.brics.tajs.lattice.State;
import dk.brics.tajs.lattice.UnknownValueResolver;
import dk.brics.tajs.lattice.Value;
import dk.brics.tajs.options.Options;
import dk.brics.tajs.util.Collections;
import org.apache.log4j.Logger;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static dk.brics.tajs.util.Collections.addToMapSet;
import static dk.brics.tajs.util.Collections.newList;
import static dk.brics.tajs.util.Collections.newMap;
import static dk.brics.tajs.util.Collections.newSet;

/**
 * Basic call and heap context sensitivities.
 */
public class BasicContextSensitivityStrategy implements IContextSensitivityStrategy {

    private static Logger log = Logger.getLogger(BasicContextSensitivityStrategy.class);

    /**
     * Parameters that should be treated context-sensitively
     */
    private final Map<Function, Set<String>> contextSensitiveParameters = newMap();

    @Override
    public HeapContext makeFunctionHeapContext(Function fun, Solver.SolverInterface c) {
        return makeHeapContext(c.getState().getContext().getFunArgs());
    }

    @Override
    public HeapContext makeActivationAndArgumentsHeapContext(State state, ObjectLabel function, Set<ObjectLabel> this_objs, FunctionCalls.CallInfo callInfo, Solver.SolverInterface c) {
        return makeHeapContext(makeContextArgumentsForCall(function, state, callInfo)); // TODO: currently ignoring this_objs (recency abstraction avoids some of the precision loss...)
    }

    @Override
    public HeapContext makeConstructorHeapContext(State state, ObjectLabel function, FunctionCalls.CallInfo callInfo, Solver.SolverInterface c) {
        return makeHeapContext(makeContextArgumentsForCall(function, state, callInfo));
    }

    private HeapContext makeHeapContext(ContextArguments funargs) {
        if (!Options.get().isContextSensitiveHeapEnabled()) {
            return null;
        }
        return HeapContext.make(funargs, null);
    }

    private ContextArguments makeContextArgumentsForCall(ObjectLabel obj_f, State edge_state, FunctionCalls.CallInfo callInfo) {
        ContextArguments funArgs = null;
        if (!Options.get().isParameterSensitivityEnabled()) {
            return null;
        }
        boolean num_actuals_unknown = callInfo.isUnknownNumberOfArgs();
        Value unknown_arg = null;
        List<Value> actuals = new ArrayList<>();
        if (num_actuals_unknown)
            unknown_arg = callInfo.getUnknownArg();
        else {
            int num_actuals = callInfo.getNumberOfArgs();
            for (int i = 0; i < num_actuals; i++)
                actuals.add(callInfo.getArg(i));
        }
        Function f = obj_f.getFunction();
        Set<String> contextSensitiveParameterNames = this.contextSensitiveParameters.get(f);
        if (contextSensitiveParameterNames != null) {
            // apply the parameter sensitivity on the chosen special vars
            if (!contextSensitiveParameterNames.isEmpty() && num_actuals_unknown) {
                // sensitive in an unknown argument value
                funArgs = new ContextArguments(unknown_arg, null);
            } else {
                // sensitive in specific argument values
                List<Value> contextSensitiveArguments = newList();
                for (String parameterName : f.getParameterNames()) {
                    Value v;
                    int i = f.getParameterNames().indexOf(parameterName);  // by construction: never -1!
                    if (contextSensitiveParameterNames.contains(parameterName) && !callInfo.isUnknownNumberOfArgs()) {
                        if (i < callInfo.getNumberOfArgs()) {
                            v = UnknownValueResolver.getRealValue(actuals.get(i), edge_state);
                        } else {
                            v = Value.makeUndef();
                        }
                    } else {
                        v = null;
                    }
                    contextSensitiveArguments.add(v);
                }
                funArgs = new ContextArguments(f.getParameterNames(), contextSensitiveArguments, null);
            }
        }
        return funArgs;
    }

    @Override
    public HeapContext makeObjectLiteralHeapContext(AbstractNode node, State state) {
        return makeHeapContext(null);
    }

    @Override
    public Context makeInitialContext() {
        Context c = new Context(null, null, null, null, null);
        if (log.isDebugEnabled())
            log.debug("creating initial context " + c);
        return c;
    }

    @Override
    public Context makeFunctionEntryContext(State state, ObjectLabel function, FunctionCalls.CallInfo callInfo, Set<ObjectLabel> this_objs, Solver.SolverInterface c) {
        assert (function.getKind() == ObjectLabel.Kind.FUNCTION);
        // set thisval for object sensitivity (unlike traditional object sensitivity we allow sets of object labels)
        Set<ObjectLabel> thisval = null;
        if (!Options.get().isObjectSensitivityDisabled()) {
            if (function.getFunction().isUsesThis()) {
                thisval = newSet(state.readThisObjects());
            }
        }
        ContextArguments contextArguments = makeContextArgumentsForCall(function, state, callInfo);

        // note: c.loopUnrolling and c.loopUnrollingsAtEntry are null by default, which will kill unrollings across calls
        Context context = new Context(thisval, contextArguments, null, null, null);

        if (log.isDebugEnabled())
            log.debug("creating function entry context " + context);
        return context;
    }

    @Override
    public Context makeForInEntryContext(Context currentContext, BeginForInNode n, Value v) {
        // reuse currentContext if possible
        int reg = n.getPropertyListRegister();
        if (currentContext.getSpecialRegisters() != null && currentContext.getSpecialRegisters().containsKey(reg) && currentContext.getSpecialRegisters().get(reg).equals(v)) {
            return currentContext;
        }

        // extend specialRegs with the given (register,value)
        Map<Integer, Value> specialRegs = null;
        if (!Options.get().isForInSpecializationDisabled()) {
            specialRegs = (currentContext.getSpecialRegisters() != null) ? newMap(currentContext.getSpecialRegisters()) : Collections.<Integer, Value>newMap();
            specialRegs.put(reg, v);
        }

        // for-in acts as entry, so update loopUnrollingsAtEntry
        Context c = new Context(currentContext.getThisVal(), currentContext.getFunArgs(), specialRegs,
                currentContext.getLoopUnrolling(), currentContext.getLoopUnrolling());

        if (log.isDebugEnabled())
            log.debug("creating for-in entry context " + c);
        return c;
    }

    @Override
    public Context makeNextLoopUnrollingContext(Context currentContext, BeginLoopNode node) {
        // update loopUnrolling
        Map<BeginLoopNode, Integer> loopUnrolling = newMap();
        if (currentContext.getLoopUnrolling() != null) {
            loopUnrolling.putAll(currentContext.getLoopUnrolling());
        }
        int nextUnrollingCount;
        if (loopUnrolling.containsKey(node)) {
            int currentUnrollingCount = loopUnrolling.get(node);
            if (currentUnrollingCount <= Options.get().getLoopUnrollings()) {
                nextUnrollingCount = currentUnrollingCount + 1;
            } else {
                // keep at max + 1 (if the count is reset to zero/removed here, it will begin increasing again!)
                if (log.isDebugEnabled())
                    log.debug("Reusing loop unrolling context " + currentContext);
                return currentContext;
            }
        } else {
            nextUnrollingCount = 0;
        }
        loopUnrolling.put(node, nextUnrollingCount);

        Context c = new Context(currentContext.getThisVal(), currentContext.getFunArgs(), currentContext.getSpecialRegisters(),
                loopUnrolling, currentContext.getLoopUnrollingsAtEntry());

        if (log.isDebugEnabled())
            log.debug("creating loop unrolling context " + c);
        return c;
    }

//    /**
//     * Constructs a new context for leaving a for-in body.
//     */
//    public static Context makeForInExitContext(Context currentContext, EndForInNode n) { // TODO: currently unused...
//        // inherit properties from currentContext
//        Context c = new Context();
//        c.thisval = currentContext.thisval;
//        c.funArgs = currentContext.funArgs;
//        c.specialVars = currentContext.specialVars;
//        c.loopUnrolling = currentContext.loopUnrolling;
//        c.loopUnrollingsAtEntry = currentContext.loopUnrollingsAtEntry;
//
//        // remove the the given register from specialRegs
//        if (currentContext.specialRegs != null) {
//            c.specialRegs = newMap(currentContext.specialRegs);
//            c.specialRegs.remove(n.getBeginNode().getPropertyListRegister()); // note: this will kill unrollings in recursive calls
//            if (c.specialRegs.isEmpty()) {
//                c.specialRegs = null;
//            }
//        }
//
//        if (log.isDebugEnabled())
//            log.debug("creating for-in exit context " + c);
//        return c;
//    }

    @Override
    public Context makeLoopExitContext(Context currentContext, EndLoopNode node) {
        // reuse currentContext if possible
        if (currentContext.getLoopUnrolling() == null || !currentContext.getLoopUnrolling().containsKey(node.getBeginNode()))
            return currentContext;

        // remove the begin-loop node from loopUnrolling
        Map<BeginLoopNode, Integer> loopUnrolling = newMap(currentContext.getLoopUnrolling());
        loopUnrolling.remove(node.getBeginNode()); // note: this will kill unrollings in recursive calls
        if (loopUnrolling.isEmpty()) {
            loopUnrolling = null;
        }

        Context c = new Context(currentContext.getThisVal(), currentContext.getFunArgs(), currentContext.getSpecialRegisters(),
                loopUnrolling, currentContext.getLoopUnrollingsAtEntry());

        if (log.isDebugEnabled())
            log.debug("creating loop unrolling exit context " + c);
        return c;
    }

    @Override
    public void requestContextSensitiveParameter(Function function, String parameter) {
        addToMapSet(this.contextSensitiveParameters, function, parameter);
    }
}