/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package edu.kit.iti.checker.property.subchecker.lattice;

import org.checkerframework.checker.initialization.InitializationTransfer;

public class LatticeTransfer extends InitializationTransfer<LatticeValue, LatticeTransfer, LatticeStore> {

    /** The Lattice type factory. */
    //protected final LatticeAnnotatedTypeFactory atypeFactory;

    /** The Lattice type factory. */
    //protected final QualifierHierarchy hierarchy;

    public LatticeTransfer(LatticeAnalysis analysis) {
        super(analysis);
    }

    /**
     * Create a new LatticeTransfer.
     *
     * @param analysis the corresponding analysis
     */
    //public LatticeTransfer(CFAbstractAnalysis<LatticeValue, LatticeStore, LatticeTransfer> analysis) {
    //    super(analysis);
    //    atypeFactory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
    //    hierarchy = atypeFactory.getQualifierHierarchy();
    //}

    enum ComparisonOperators {
        EQUAL,
        NOT_EQUAL,
        GREATER_THAN,
        GREATER_THAN_EQ,
        LESS_THAN,
        LESS_THAN_EQ;
    }


}
