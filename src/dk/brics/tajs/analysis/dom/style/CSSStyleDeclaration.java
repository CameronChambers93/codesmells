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

package dk.brics.tajs.analysis.dom.style;

import dk.brics.tajs.analysis.InitialStateBuilder;
import dk.brics.tajs.analysis.PropVarOperations;
import dk.brics.tajs.analysis.Solver;
import dk.brics.tajs.analysis.dom.DOMObjects;
import dk.brics.tajs.lattice.ObjectLabel;
import dk.brics.tajs.lattice.State;
import dk.brics.tajs.lattice.Value;

import java.util.Collections;

public class CSSStyleDeclaration {

    public static ObjectLabel STYLEDECLARATION;

    public static void build(Solver.SolverInterface c) {
        State s = c.getState();
        PropVarOperations pv = c.getAnalysis().getPropVarOperations();
        STYLEDECLARATION = new ObjectLabel(DOMObjects.CSSSTYLEDECLARATION, ObjectLabel.Kind.OBJECT);

        s.newObject(STYLEDECLARATION);
        s.writeInternalPrototype(STYLEDECLARATION, Value.makeObject(InitialStateBuilder.OBJECT_PROTOTYPE));
        pv.writeProperty(Collections.singleton(STYLEDECLARATION), Value.makeAnyStrNotUInt(), Value.makeAnyStr(), false, true);
        s.multiplyObject(STYLEDECLARATION);
        STYLEDECLARATION = STYLEDECLARATION.makeSingleton().makeSummary();
    }
}
