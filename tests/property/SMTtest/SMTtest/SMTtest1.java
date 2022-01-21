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

import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

public class SMTtest1 {
	

	public int c = 1 + 2 * 2;
	public int r = 1 + 2 * 3 / 4 + 5 * 6 - 7 / 8 / 9;
	public final int x = 0 / 5;
	
	// :: error: assignment.type.incompatible
	@Interval(min="0", max="c") int a = 1 + r;


}
