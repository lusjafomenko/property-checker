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
package smt_test;
import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

public class SMTtestMethod {


	public final int maxAge = 150;
	final @Interval(min = "0", max = "100") int area = 20;
	final @Interval(min = "0", max = "maxAge") int age;
	
	public SMTtestMethod() {
		this.age = 20;
	}
	
	public SMTtestMethod(@Interval(min = "0", max = "150") int age1) {
		this.age = age1;
	}
	
	//public @Less(value = "5") int v1 = 2;

	public final int z = 10;
	int ten = 10;
	int nine = 9;
	public final @Interval(min = "0", max = "z") int x = 1;
	String s = "ImAString";
	
	
	final int are1 = area;
	final int gardenArea = 50;
	final int noEntryArea = 10;
	final int maximum = 1000;
	
	//public @Less(value = "z") int l = 9;
	//public @Less(value = "z") int l1 = x;
	
	//public @Interval(min = "0", max = "z") int t1 = x;
	public @Interval(min = "0", max = "x + 1") int t = 1 + 0 + 0;
	
	//public @Interval(min = "0", max = "x") int t3 = z + 5;
	
	
	public @Interval(min = "0", max = "maximum") int maxInv = (area + gardenArea - noEntryArea) / 3;
	
	//@Interval(min = "0", max = "z") int testVar = dummy();

	public static @Interval(min = "0", max = "z") int dummy() {
		//@Interval(min = "0", max = "z") int t1 = 5 + 1;
		int m1 = 0;
		return m1;
	}
	
	public @Interval(min = "0", max = "m") int dummy2(@Interval(min = "0", max = "ten") int m) {
		int m2 = m;
		return m2;
	}
	
	public static @Interval(min = "1 * x", max = "m + 1 * 1") int dummy3(@Interval(min = "0", max = "nine") int m, int second) {
		int m3 = m + 1;
		@Interval(min = "0", max = "maximum") int dummyVar1 = 6;
		return m3;
	}
	
	public @Interval(min = "0", max = "maxInv") int calculateInv() {
		int inv = 4;
		inv = 5;
		inv = 4 + 1;
		inv = x * t;
		@Interval(min = "0", max = "maximum") int forInv = dummy3(5, 5);
		@Interval(min = "0", max = "maximum") int dummyVar = 6;
		//inv = dummy3(5, 5);
		inv = forInv;
		return inv;
	}
	
	public @Interval(min = "m % 2", max = "m + 1 * 1") int dummy4(@Interval(min = "0", max = "maximum") int m) {
		int m4 = m + 1;
		@Interval(min = "0", max = "gardenArea") int t8 = calculateInv();
		@Interval(min = "0", max = "10") int firstVar = 9;
		@Interval(min = "0", max = "area") int secondVar = area;
		return m4;
	}
	
	public static void main(String[] args) {
		int eight = 8;
		int r = 10;
		@Interval(min = "0", max = "z") int t6 = dummy3(eight, eight);
		@Interval(min = "0", max = "area + 1") int t2 = dummy3(31, eight);
		//final int x = 1;
		@Interval(min = "0", max = "z") int t3 = t6;
		@Interval(min = "x", max = "ten") int t10 = dummy3(4, r);
		
		
		
	}


}


	
