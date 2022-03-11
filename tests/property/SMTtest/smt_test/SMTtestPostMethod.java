package smt_test;

import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

public class SMTtestPostMethod {
	
	@Less(value="10") int vp = 5;
	int tttp = 10;
	int twwwo = 2;
	int onne = 1;
	int thousend = 1000;
	
	
	public void testPostMethod() {
		SMTtestMethod mp = new SMTtestMethod();
		//int twenty = m.age;
		@Interval(min = "0", max = "tttp") int tenp = mp.x;
		@Interval(min = "0", max = "tttp") int fieldAccess = 10;
		SMTtestMethod ma = new SMTtestMethod(10);
		@Interval(min = "0", max = "tttp") int aggg = ma.age;
		@Interval(min = "0", max = "ma.age") int ageField = ma.age;
		fieldAccess = ma.age;
		
		// :: error: argument.type.incompatible
		SMTtestMethod mb = new SMTtestMethod(180);
		
		@Interval(min = "0", max = "thousend") int agerr = mb.age;
		@Length1(min = "onne", max = "onne") List li1 = new List("DEF");
		SMTtestMethod uninit;
		
	}
}
