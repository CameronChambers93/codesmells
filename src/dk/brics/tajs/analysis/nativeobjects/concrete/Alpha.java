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

package dk.brics.tajs.analysis.nativeobjects.concrete;

import dk.brics.tajs.analysis.PropVarOperations;
import dk.brics.tajs.analysis.Solver;
import dk.brics.tajs.analysis.nativeobjects.JSArray;
import dk.brics.tajs.flowgraph.AbstractNode;
import dk.brics.tajs.lattice.HeapContext;
import dk.brics.tajs.lattice.ObjectLabel;
import dk.brics.tajs.lattice.Value;

import java.util.Map;
import java.util.Set;

import static dk.brics.tajs.util.Collections.newMap;
import static dk.brics.tajs.util.Collections.singleton;

/**
 * Converts concrete values to abstract values.
 */
public class Alpha {

    public static Value createNewArrayValue(ConcreteArray array, AbstractNode sourceNode, Solver.SolverInterface c) {
        PropVarOperations pv = c.getAnalysis().getPropVarOperations();
        final Map<String, Value> map = newMap();
        map.put("<CONCRETE>", Value.makeStr(array.toSourceCode()));
        ObjectLabel label = JSArray.makeArray(sourceNode, Value.makeNum(array.getLength()), HeapContext.make(null, map), c);
        Set<ObjectLabel> labels = singleton(label);
        array.getExtraProperties().forEach((String k, ConcreteValue v) -> pv.writeProperty(labels, Value.makeTemporaryStr(k), toValue(v), false, true));
        for (int i = 0; i < array.getLength(); i++) {
            final Value index = Value.makeStr(String.valueOf(i));
            ConcreteValue concreteValue = array.get(i);
            final Value value = toValue(concreteValue);
            pv.writeProperty(labels, index, value, false, true);
        }
        return Value.makeObject(label);
    }

    public static Value toValue(PrimitiveConcreteValue concreteValue) {
        return toValue((ConcreteValue) concreteValue);
    }

    private static Value toValue(ConcreteValue concreteValue) { // convenience signature to be used internally
        return concreteValue.accept(new ConcreteValueVisitor<Value>() {
            @Override
            public Value visit(ConcreteNumber v) {
                double number = v.getNumber();
                if (Double.isNaN(number)) {
                    return Value.makeNumNaN();
                }
                if (Double.isInfinite(number)) {
                    return Value.makeNumInf();
                }
                return Value.makeNum(number);
            }

            @Override
            public Value visit(ConcreteString v) {
                return Value.makeStr(v.getString());
            }

            @Override
            public Value visit(ConcreteArray v) {
                throw new IllegalArgumentException("Can only create arrays explicitly: use createNewArrayValue instead!");
            }

            @Override
            public Value visit(ConcreteUndefined v) {
                return Value.makeUndef();
            }

            @Override
            public Value visit(ConcreteRegularExpression v) {
                throw new IllegalArgumentException("Can not create new regular expressions");
            }

            @Override
            public Value visit(ConcreteNull v) {
                return Value.makeNull();
            }

            @Override
            public Value visit(ConcreteBoolean v) {
                return Value.makeBool(v.getBooleanValue());
            }
        });
    }
}
