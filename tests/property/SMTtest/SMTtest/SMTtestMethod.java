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

public class SMTtestMethod {
	
	public final int z = 10;
	public final int x = 1;
	
	final int area = 20;
	final int gardenArea = 50;
	final int noEntryArea = 10;
	
	//public @Interval(min = "0", max = "z") int t1 = x;
	public @Interval(min = "0", max = "x") int t = 1 + 0;
	
	//public @Interval(min = "0", max = "x") int t3 = z + 5;
	
	
	int maxInv = (area + gardenArea - noEntryArea) / 3;
	
	//@Interval(min = "0", max = "z") int testVar = dummy();

	public @Interval(min = "0", max = "z") int dummy() {
		//@Interval(min = "0", max = "z") int t1 = 5 + 1;
		int m1 = 0;
		return m1;
	}
	
	public @Interval(min = "0", max = "m") int dummy2(@Interval(min = "0", max = "z") int m) {
		int m2 = m;
		return m2;
	}
	
	public @Interval(min = "1 * x", max = "m + 1 * 1") int dummy3(@Interval(min = "0", max = "z") int m) {
		int m2 = m + 1;
		return m2;
	}
	
	public @Interval(min = "0", max = "maxInv") int calculateInv() {
		int inv = 4;
		return inv;
	}
	
	public @Interval(min = "m % 2", max = "m + 1 * 1") int dummy4(@Interval(min = "0", max = "z") int m) {
		int m2 = m + 1;
		return m2;
	}
	
	public static void main(String[] args) {
		@Interval(min = "0", max = "area") int t2 = 5 + 1;
		//final int x = 1;
		
		
	}


}


	
