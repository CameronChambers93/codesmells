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

package dk.brics.tajs.options;

import dk.brics.tajs.util.AnalysisException;
import org.apache.log4j.Appender;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;
import org.kohsuke.args4j.Argument;
import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;
import org.kohsuke.args4j.Option;

import java.io.OutputStream;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import static dk.brics.tajs.util.Collections.newSet;

/**
 * Option values.
 * <p>
 * All options are disabled by default.
 */
public class OptionValues {

    @Option(name = "-no-control-sensitivity", usage = "Disable control sensitivity")
    private boolean noControlSensitivity;

    @Option(name = "-no-object-sensitivity", usage = "Disable object sensitivity")
    private boolean noObjectSensitivity;

    @Option(name = "-no-recency", usage = "Disable recency abstraction")
    private boolean noRecency;

    @Option(name = "-no-modified", usage = "Disable modified flags")
    private boolean noModified;

    @Option(name = "-no-exceptions", usage = "Disable implicit exception flow")
    private boolean noExceptions;

    @Option(name = "-no-gc", usage = "Disable abstract garbage collection")
    private boolean noGc;

    @Option(name = "-no-lazy", usage = "Disable lazy propagation")
    private boolean noLazy;

    @Option(name = "-no-copy-on-write", usage = "Disable copy-on-write")
    private boolean noCopyOnWrite;

    @Option(name = "-no-hybrid-collections", usage = "Disable hybrid collections")
    private boolean noHybridCollections;

    @Option(name = "-no-charged-calls", usage = "Disable charged calls")
    private boolean noChargedCalls;

    @Option(name = "-no-concrete", usage = "Disable concrete interpretation for selected native functions")
    private boolean noConcreteNative;

    @Option(name = "-no-for-in", usage = "Disable for-in specialization")
    private boolean noForInSpecialization;

//	@Optional(name = "-flowgraph-optimization", usage = "Enable flowgraph optimization")
//	private boolean flowgraphOptimization;

    @Option(name = "-context-specialization", usage = "Enable context specialization")
    private boolean contextSpecialization;

    @Option(name = "-low-severity", usage = "Enable low severity messages")
    private boolean lowSeverity;

    @Option(name = "-unsound", usage = "Enable unsound assumptions")
    private boolean unsound;

    @Option(name = "-flowgraph", usage = "Output flowgraph.dot")
    private boolean flowgraph;

    @Option(name = "-callgraph", usage = "Output callgraph.dot")
    private boolean callgraph;

    @Option(name = "-debug", usage = "Output debug information")
    private boolean debug;

    @Option(name = "-show-variable-info", usage = "Output type and line information for variables")
    private boolean showVariableInfo;

    @Option(name = "-newflow", usage = "Report summary of new flow at function entries")
    private boolean newflow;

    @Option(name = "-states", usage = "Output intermediate abstract states")
    private boolean states;

    @Option(name = "-test", usage = "Test mode (implies quiet), ensures predictable iteration orders")
    private boolean test;

    @Option(name = "-test-flowgraph-builder", usage = "Test flow graph builder (implies test mode)")
    private boolean testFlowgraphBuilder;

    @Option(name = "-timing", usage = "Report analysis time")
    private boolean timing;

    @Option(name = "-statistics", usage = "Report statistics")
    private boolean statistics;

    @Option(name = "-memory-usage", usage = "Report the memory usage of the analysis")
    private boolean memoryUsage;

    @Option(name = "-quiet", usage = "Only output results, not progress")
    private boolean quiet;

    @Option(name = "-dom", usage = "Enable Mozilla DOM browser model")
    private boolean includeDom;

    @Option(name = "-propagate-dead-flow", usage = "Propagate empty values")
    private boolean propagateDeadFlow;

    @Option(name = "-always-canput", usage = "Assume [[CanPut]] always succeeds")
    private boolean alwaysCanput;

    @Option(name = "-eval-statistics", usage = "Report uses of eval and innerHTML")
    private boolean evalStatistics;

    @Option(name = "-coverage", usage = "Output a view of the source with unreachable lines highlighted")
    private boolean coverage;

//	@Optional(name = "-introduce-error", usage = "Measure precision by randomly introducing syntax errors")
//	private boolean introduceError;

    @Option(name = "-no-messages", usage = "Disable analysis messages")
    private boolean no_messages;

    @Option(name = "-single-event-handler-type", usage = "Do not distinguish between different types of event handlers")
    private boolean single_event_handler_type;

    @Option(name = "-ignore-html-content", usage = "Ignore the content of the HTML page")
    private boolean ignore_html_content;

    @Option(name = "-uneval", usage = "Try to remove calls to eval")
    private boolean unevalizer;

    @Option(name = "-no-polymorphic", usage = "Disable use of polymorphic objects")
    private boolean no_polymorphic;

    @Option(name = "-return-json", usage = "Assume that AJAX calls return JSON")
    private boolean ajaxReturnsJson;

    @Option(name = "-help", usage = "Prints this message")
    private boolean help;

    @Option(name = "-ignore-libraries", usage = "Ignore unreachable code messages from libraries (library names separated by comma)")
    private String ignoredLibrariesString;

    private Set<String> ignoredLibraries = new LinkedHashSet<>();

    @Option(name = "-context-sensitive-heap", usage = "Enable selective context sensitive heap abstractions")
    private boolean contextSensitiveHeap;

    @Option(name = "-parameter-sensitivity", usage = "Enabled usage of different contexts for (some) calls based on the argument values")
    private boolean parameterSensitivity;

    @Option(name = "-ignore-unreachable", usage = "Ignore code parts which has been marked as unreachable")
    private boolean ignoreUnreachable;

    @Option(name = "-loop-unrolling", usage = "Enables unrolling of loops up to [n] times")
    private int loopUnrollings = -1;

    @Option(name = "-determinacy", usage = "Enables all of the techniques described in 'Determinacy in Static Analysis of jQuery', OOPSLA 2014")
    private boolean determinacy;

    @Option(name = "-polyfill-mdn", usage = "Enables use of polyfills from the Mozilla Developer Network web pages")
    private boolean polyfillMDN;

    @Option(name = "-polyfill-es6-collections", usage = "Enables use of polyfills for ES6 collections")
    private boolean polyfillES6Collections;

    @Option(name = "-polyfill-typed-arrays", usage = "Enables use of polyfills for typed arrays (Int8Array, Float64Array ...)")
    private boolean polyfillTypedArrays;

    @Option(name = "-async-events", usage = "Enables execution of asynchronous event handlers with TAJS_asyncListen")
    private boolean asyncEvents;

    @Argument
    private List<String> arguments = new ArrayList<>();

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        OptionValues that = (OptionValues) o;

        if (noControlSensitivity != that.noControlSensitivity) return false;
        if (noObjectSensitivity != that.noObjectSensitivity) return false;
        if (noRecency != that.noRecency) return false;
        if (noModified != that.noModified) return false;
        if (noExceptions != that.noExceptions) return false;
        if (noGc != that.noGc) return false;
        if (noLazy != that.noLazy) return false;
        if (noCopyOnWrite != that.noCopyOnWrite) return false;
        if (noHybridCollections != that.noHybridCollections) return false;
        if (noChargedCalls != that.noChargedCalls) return false;
        if (noConcreteNative != that.noConcreteNative) return false;
        if (noForInSpecialization != that.noForInSpecialization) return false;
        if (contextSpecialization != that.contextSpecialization) return false;
        if (lowSeverity != that.lowSeverity) return false;
        if (unsound != that.unsound) return false;
        if (flowgraph != that.flowgraph) return false;
        if (callgraph != that.callgraph) return false;
        if (debug != that.debug) return false;
        if (showVariableInfo != that.showVariableInfo) return false;
        if (newflow != that.newflow) return false;
        if (states != that.states) return false;
        if (test != that.test) return false;
        if (testFlowgraphBuilder != that.testFlowgraphBuilder) return false;
        if (timing != that.timing) return false;
        if (statistics != that.statistics) return false;
        if (memoryUsage != that.memoryUsage) return false;
        if (quiet != that.quiet) return false;
        if (includeDom != that.includeDom) return false;
        if (propagateDeadFlow != that.propagateDeadFlow) return false;
        if (alwaysCanput != that.alwaysCanput) return false;
        if (evalStatistics != that.evalStatistics) return false;
        if (coverage != that.coverage) return false;
        if (no_messages != that.no_messages) return false;
        if (single_event_handler_type != that.single_event_handler_type) return false;
        if (ignore_html_content != that.ignore_html_content) return false;
        if (unevalizer != that.unevalizer) return false;
        if (no_polymorphic != that.no_polymorphic) return false;
        if (ajaxReturnsJson != that.ajaxReturnsJson) return false;
        if (help != that.help) return false;
        if (contextSensitiveHeap != that.contextSensitiveHeap) return false;
        if (parameterSensitivity != that.parameterSensitivity) return false;
        if (ignoreUnreachable != that.ignoreUnreachable) return false;
        if (loopUnrollings != that.loopUnrollings) return false;
        if (determinacy != that.determinacy) return false;
        if (polyfillMDN != that.polyfillMDN) return false;
        if (polyfillES6Collections != that.polyfillES6Collections) return false;
        if (polyfillTypedArrays != that.polyfillTypedArrays) return false;
        if (asyncEvents != that.asyncEvents) return false;
        if (ignoredLibrariesString != null ? !ignoredLibrariesString.equals(that.ignoredLibrariesString) : that.ignoredLibrariesString != null)
            return false;
        if (ignoredLibraries != null ? !ignoredLibraries.equals(that.ignoredLibraries) : that.ignoredLibraries != null)
            return false;
        return arguments != null ? arguments.equals(that.arguments) : that.arguments == null;
    }

    @Override
    public int hashCode() {
        int result = (noControlSensitivity ? 1 : 0);
        result = 31 * result + (noObjectSensitivity ? 1 : 0);
        result = 31 * result + (noRecency ? 1 : 0);
        result = 31 * result + (noModified ? 1 : 0);
        result = 31 * result + (noExceptions ? 1 : 0);
        result = 31 * result + (noGc ? 1 : 0);
        result = 31 * result + (noLazy ? 1 : 0);
        result = 31 * result + (noCopyOnWrite ? 1 : 0);
        result = 31 * result + (noHybridCollections ? 1 : 0);
        result = 31 * result + (noChargedCalls ? 1 : 0);
        result = 31 * result + (noConcreteNative ? 1 : 0);
        result = 31 * result + (noForInSpecialization ? 1 : 0);
        result = 31 * result + (contextSpecialization ? 1 : 0);
        result = 31 * result + (lowSeverity ? 1 : 0);
        result = 31 * result + (unsound ? 1 : 0);
        result = 31 * result + (flowgraph ? 1 : 0);
        result = 31 * result + (callgraph ? 1 : 0);
        result = 31 * result + (debug ? 1 : 0);
        result = 31 * result + (showVariableInfo ? 1 : 0);
        result = 31 * result + (newflow ? 1 : 0);
        result = 31 * result + (states ? 1 : 0);
        result = 31 * result + (test ? 1 : 0);
        result = 31 * result + (testFlowgraphBuilder ? 1 : 0);
        result = 31 * result + (timing ? 1 : 0);
        result = 31 * result + (statistics ? 1 : 0);
        result = 31 * result + (memoryUsage ? 1 : 0);
        result = 31 * result + (quiet ? 1 : 0);
        result = 31 * result + (includeDom ? 1 : 0);
        result = 31 * result + (propagateDeadFlow ? 1 : 0);
        result = 31 * result + (alwaysCanput ? 1 : 0);
        result = 31 * result + (evalStatistics ? 1 : 0);
        result = 31 * result + (coverage ? 1 : 0);
        result = 31 * result + (no_messages ? 1 : 0);
        result = 31 * result + (single_event_handler_type ? 1 : 0);
        result = 31 * result + (ignore_html_content ? 1 : 0);
        result = 31 * result + (unevalizer ? 1 : 0);
        result = 31 * result + (no_polymorphic ? 1 : 0);
        result = 31 * result + (ajaxReturnsJson ? 1 : 0);
        result = 31 * result + (help ? 1 : 0);
        result = 31 * result + (ignoredLibrariesString != null ? ignoredLibrariesString.hashCode() : 0);
        result = 31 * result + (ignoredLibraries != null ? ignoredLibraries.hashCode() : 0);
        result = 31 * result + (contextSensitiveHeap ? 1 : 0);
        result = 31 * result + (parameterSensitivity ? 1 : 0);
        result = 31 * result + (ignoreUnreachable ? 1 : 0);
        result = 31 * result + loopUnrollings;
        result = 31 * result + (determinacy ? 1 : 0);
        result = 31 * result + (polyfillMDN ? 1 : 0);
        result = 31 * result + (polyfillES6Collections ? 1 : 0);
        result = 31 * result + (polyfillTypedArrays ? 1 : 0);
        result = 31 * result + (asyncEvents ? 1 : 0);
        result = 31 * result + (arguments != null ? arguments.hashCode() : 0);
        return result;
    }

    public OptionValues() {
        this(null, null);
    }

    public OptionValues(OptionValues base) {
        this(base, null);
    }

    public OptionValues(OptionValues base, String[] args) {
        if (base != null) {
            // copy values from base
            for (Field f : OptionValues.class.getDeclaredFields()) {
                f.setAccessible(true);
                try {
                    Object value = f.get(base);
                    if (value instanceof Cloneable) {
                        for (Method possibleClone : value.getClass().getDeclaredMethods()) {
                            possibleClone.setAccessible(true);
                            if ("clone".equals(possibleClone.getName()) && possibleClone.getParameterTypes().length == 0) {
                                value = possibleClone.invoke(value);
                            }
                        }
                    }
                    f.set(this, value);
                } catch (IllegalArgumentException | IllegalAccessException | InvocationTargetException e) {
                    throw new RuntimeException(e);
                }
            }
        }
        if (args != null) {
            // parse args
            CmdLineParser parser = new CmdLineParser(this);
            try {
                parser.parseArgument(args);
                // handle flags that have side-effects, for example imply other flags
                if (ignoredLibrariesString != null && !ignoredLibrariesString.isEmpty()) {
                    ignoredLibraries = newSet(Arrays.asList(ignoredLibrariesString.split(",")));
                }
                if (determinacy) {
                    enableDeterminacy();
                }
                if (test) {
                    enableTest();
                }
                if (testFlowgraphBuilder) {
                    enableTestFlowGraphBuiler();
                }
                if (debug) {
                    enableDebug();
                }
                if (help) {
                    describe(System.out);
                }
            } catch (CmdLineException e) {
                throw new RuntimeException("Bad arguments: " + e.getMessage());
            }
        }
    }

    public OptionValues(String[] args) {
        this(null, args);
    }

    @Override
    protected OptionValues clone() {
        return new OptionValues(this);
    }

    /**
     * Prints a description of the available options.
     */
    public void describe(OutputStream out) {
        new CmdLineParser(this).printUsage(out);
    }

    public Map<String, Object> getOptionValues() {
        try {
            Map<String, Object> options = new TreeMap<>();
            for (Field f : OptionValues.class.getDeclaredFields()) {
                f.setAccessible(true);
                Option annotation = f.getAnnotation(Option.class);
                if (annotation != null) {
                    Object value = f.get(this);
                    String name = annotation.name();
                    if (value != null && ((value instanceof Boolean && (Boolean) value) ||
                            (value instanceof Integer && ((Integer) value) != -1) ||
                            (value instanceof String && !"".equals(value) && !"-1".equals(value)) ||
                            (value instanceof Collection && !((Collection<?>) value).isEmpty()))) {
                        options.put(name, value);
                    }
                }
            }
            return options;
        } catch (IllegalArgumentException | IllegalAccessException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (Entry<String, Object> me : getOptionValues().entrySet()) {
            if (!first) {
                sb.append(" ");
            } else {
                first = false;
            }
            sb.append(me.getKey());
            if (!(me.getValue() instanceof Boolean)) {
                sb.append(" ").append(me.getValue());
            }
        }
        for (String argument : arguments) {
            if (!first) {
                sb.append(" ");
            } else {
                first = false;
            }
            sb.append(argument);
        }
        return sb.toString();
    }

    public void disableAjaxReturnsJson() {
        ajaxReturnsJson = false;
    }

    public void disableAlwaysCanPut() {
        alwaysCanput = false;
    }

    public void disableCallgraph() {
        callgraph = false;
    }

    public void disableShowVariableInfo() {
        showVariableInfo = false;
    }

    public void disableContextSensitiveHeap() {
        contextSensitiveHeap = false;
    }

    public void disableContextSpecialization() {
        contextSpecialization = false;
    }

    public void disableControlSensitivity() {
        noControlSensitivity = true;
    }

    public void disableDebug() {
        debug = false;
        Logger.getRootLogger().setLevel(Level.INFO);
        Logger.getRootLogger().getAppender("tajs").setLayout(new PatternLayout("%m%n"));
    }

    public void disableFlowgraph() {
        flowgraph = false;
    }

//	public void disableFlowgraphOptimization() {
//		flowgraphOptimization = false;
//	}

    public void disableNoForInSpecialization() {
        noForInSpecialization = false;
    }

    public void disableIgnoreHTMLContent() {
        ignore_html_content = false;
    }

    public void disableIgnoreLibraries() {
        ignoredLibrariesString = "";
        ignoredLibraries = newSet();
    }

    public void disableIncludeDom() {
        includeDom = false;
    }

    public void disableLowSeverity() {
        lowSeverity = false;
    }

    public void disableLoopUnrolling() {
        this.loopUnrollings = -1;
    }

    public void disableMemoryUsage() {
        memoryUsage = false;
    }

    public void disableNewflow() {
        newflow = false;
    }

    public void disableNoChargedCalls() {
        noChargedCalls = false;
    }

    public void disableNoCopyOnWrite() {
        noCopyOnWrite = false;
    }

    public void disableNoExceptions() {
        noExceptions = false;
    }

    public void disableNoGc() {
        noGc = false;
    }

    public void disableNoHybridCollections() {
        noHybridCollections = false;
    }

    public void disableNoLazy() {
        noLazy = false;
    }

    public void disableNoMessages() {
        no_messages = false;
    }

    public void disableNoModified() {
        noModified = false;
    }

    public void disableNoObjectSensitivity() {
        noObjectSensitivity = false;
    }

    public void disableNoPolymorphic() {
        no_polymorphic = false;
    }

    public void disableNoRecency() {
        noRecency = false;
    }

    public void disableDeterminacy() {
        determinacy = false;
    }

    public void disableParameterSensitivity() {
        parameterSensitivity = false;
    }

    public void disablePropagateDeadFlow() {
        propagateDeadFlow = false;
    }

    public void disableQuiet() {
        quiet = false;
    }

    public void disableSingleEventHandlerType() {
        single_event_handler_type = false;
    }

    public void disableStates() {
        states = false;
    }

    public void disableStatistics() {
        statistics = false;
    }

    public void disableTest() {
        test = false;
        quiet = false;
        lowSeverity = false;
    }

    public void disableTestFlowGraphBuilder() {
        disableTest();
        testFlowgraphBuilder = false;
    }

    public void disableTiming() {
        timing = false;
    }

    public void disableUnevalizer() {
        unevalizer = false;
    }

    public void disableUnreachable() {
        ignoreUnreachable = false;
    }

    public void disableUnsound() {
        unsound = false;
    }

    public void enableAjaxReturnsJson() {
        ajaxReturnsJson = true;
    }

    public void enableAlwaysCanPut() {
        alwaysCanput = true;
    }

    public void enableCallgraph() {
        callgraph = true;
    }

    public void enableShowVariableInfo() {
        showVariableInfo = true;
    }

//	public void enableErrorBatchMode() {
//		introduceError = true;
//	}

    public void enableContextSensitiveHeap() {
        contextSensitiveHeap = true;
    }

    public void enableContextSpecialization() {
        contextSpecialization = true;
    }

//	public void enableFlowgraphOptimization() {
//		flowgraphOptimization = true;
//	}

    public void enableControlSensitivity() {
        noControlSensitivity = false;
    }

    public void enableCoverage() {
        coverage = true;
    }

    public void enableDebug() {
        debug = true;
        Logger.getRootLogger().setLevel(Level.DEBUG);
        Appender a = Logger.getRootLogger().getAppender("tajs");
        if (a != null)
            a.setLayout(new PatternLayout("[%p %C{1}] %m%n"));
    }

    public void enableEvalStatistics() {
        evalStatistics = true;
    }

    public void enableFlowgraph() {
        flowgraph = true;
    }

    public void enableNoForInSpecialization() {
        noForInSpecialization = true;
    }

    public void enableIgnoreHTMLContent() {
        ignore_html_content = true;
    }

    public void enableIncludeDom() {
        includeDom = true;
    }

    public void enableLowSeverity() {
        lowSeverity = true;
    }

    public void enableLoopUnrolling(int loopUnrollings) {
        this.loopUnrollings = loopUnrollings;
    }

    public void enableMemoryUsage() {
        memoryUsage = true;
    }

    public void enableNewflow() {
        newflow = true;
    }

    public void enableNoChargedCalls() {
        noChargedCalls = true;
    }

    public void enableNoCopyOnWrite() {
        noCopyOnWrite = true;
    }

    public void enableNoExceptions() {
        noExceptions = true;
    }

    public void enableNoGc() {
        noGc = true;
    }

    public void enableNoHybridCollections() {
        noHybridCollections = true;
    }

    public void enableNoLazy() {
        noLazy = true;
    }

    public void enableNoMessages() {
        no_messages = true;
    }

    public void enableNoModified() {
        noModified = true;
    }

    public void enableNoObjectSensitivity() {
        noObjectSensitivity = true;
    }

    public void enableNoPolymorphic() {
        no_polymorphic = true;
    }

    public void enableNoRecency() {
        noRecency = true;
    }

    public void enableDeterminacy() {
        determinacy = true;
        enableContextSensitiveHeap();
        enableParameterSensitivity();
        enableLoopUnrolling(50);
    }

    public void enableParameterSensitivity() {
        parameterSensitivity = true;
    }

    public void enablePropagateDeadFlow() {
        propagateDeadFlow = true;
    }

    public void enableQuiet() {
        quiet = true;
    }

    public void enableSingleEventHandlerType() {
        single_event_handler_type = true;
    }

    public void enableStates() {
        states = true;
    }

    public void enableStatistics() {
        statistics = true;
    }

    public void enableTest() {
        test = true;
        quiet = true;
        lowSeverity = true;
    }

    public void enableTestFlowGraphBuiler() {
        enableTest();
        testFlowgraphBuilder = true;
    }

    public void enableTiming() {
        timing = true;
    }

    public void enableUnevalizer() {
        unevalizer = true;
    }

    public void enableUnreachable() {
        ignoreUnreachable = true;
    }

    public void enableUnsound() {
        unsound = true;
    }

    public List<String> getArguments() {
        return arguments;
    }

    public Set<String> getLibraries() {
        return ignoredLibraries;
    }

    public int getLoopUnrollings() {
        return loopUnrollings;
    }

    public boolean isAlwaysCanPut() {
        return alwaysCanput;
    }

    public boolean isCallGraphEnabled() {
        return callgraph;
    }

//	public boolean isErrorBatchMode() {
//		return introduceError;
//	}

    public boolean isChargedCallsDisabled() {

        return noChargedCalls;
    }

    public boolean isShowVariableInfoEnabled() {
        return showVariableInfo;
    }

    public boolean isContextSensitiveHeapEnabled() {
        return contextSensitiveHeap;
    }

//	public boolean isFlowGraphOptimizationEnabled() {
//		return flowgraphOptimization;
//	}

    public boolean isContextSpecializationEnabled() {
        return contextSpecialization;
    }

    public boolean isControlSensitivityDisabled() {
        return noControlSensitivity;
    }

    public boolean isCopyOnWriteDisabled() {
        return noCopyOnWrite;
    }

    public boolean isCoverageEnabled() {
        return coverage;
    }

    public boolean isDebugEnabled() {
        return debug;
    }

    public boolean isDebugOrTestEnabled() {
        return debug || test;
    }

    public boolean isDOMEnabled() {
        return includeDom;
    }

    public boolean isEvalStatistics() {
        return evalStatistics;
    }

    public boolean isExceptionsDisabled() {
        return noExceptions;
    }

    public boolean isFlowGraphEnabled() {
        return flowgraph;
    }

    public boolean isForInSpecializationDisabled() {
        return noForInSpecialization;
    }

    public boolean isGCDisabled() {
        return noGc;
    }

    public boolean isHybridCollectionsDisabled() {
        return noHybridCollections;
    }

    public boolean isIgnoreHTMLContent() {
        return ignore_html_content;
    }

    public boolean isIgnoreLibrariesEnabled() {
        return !ignoredLibraries.isEmpty();
    }

    public boolean isIntermediateStatesEnabled() {
        return states;
    }

    public boolean isLazyDisabled() {
        return noLazy;
    }

    public boolean isLowSeverityEnabled() {
        return lowSeverity;
    }

    public boolean isLoopUnrollingEnabled() {
        return loopUnrollings != -1;
    }

    public boolean isMemoryMeasurementEnabled() {
        return memoryUsage;
    }

    public boolean isModifiedDisabled() {
        return noModified;
    }

    public boolean isNewFlowEnabled() {
        return newflow;
    }

    public boolean isNoMessages() {
        return no_messages;
    }

    public boolean isObjectSensitivityDisabled() {
        return noObjectSensitivity;
    }

    public boolean isDeterminacyEnabled() {
        return determinacy;
    }

    public boolean isParameterSensitivityEnabled() {
        return parameterSensitivity;
    }

    public boolean isPolymorphicDisabled() {
        return no_polymorphic;
    }

    public boolean isPropagateDeadFlow() {
        return propagateDeadFlow;
    }

    public boolean isQuietEnabled() {
        return quiet;
    }

    public boolean isRecencyDisabled() {
        return noRecency;
    }

    public boolean isReturnJSON() {
        return ajaxReturnsJson;
    }

    public boolean isSingleEventHandlerType() {
        return single_event_handler_type;
    }

    public boolean isStatisticsEnabled() {
        return statistics;
    }

    public boolean isTestEnabled() {
        return test;
    }

    public boolean isTestFlowGraphBuilderEnabled() {
        return testFlowgraphBuilder;
    }

    public boolean isTimingEnabled() {
        return timing;
    }

    public boolean isUnevalizerEnabled() { // TODO: (#9) enable unevalizer by default? (affects use of live variables!)
        return unevalizer;
    }

    public boolean isIgnoreUnreachableEnabled() {
        return ignoreUnreachable;
    }

    public boolean isConcreteNativeDisabled() {
        return noConcreteNative;
    }

    public boolean isUnsoundEnabled() {
        return unsound;
    }

    public void checkConsistency() {
        if (arguments == null || arguments.isEmpty()) {
            throw new AnalysisException("No arguments provided!");
        }
    }

    public void enablePolyfillMDN() {
        polyfillMDN = true;
    }

    public void enablePolyfillES6Collections() {
        polyfillES6Collections = true;
    }

    public void enablePolyfillTypedArrays() {
        polyfillTypedArrays = true;
    }

    public boolean isPolyfillMDNEnabled() {
        return polyfillMDN;
    }

    public boolean isPolyfillES6CollectionsEnabled() {
        return polyfillES6Collections;
    }

    public boolean isPolyfillTypedArraysEnabled() {
        return polyfillTypedArrays;
    }

    public void enableAsyncEvents() {
        asyncEvents = true;
    }

    public boolean isAsyncEventsEnabled() {
        return asyncEvents;
    }
}
