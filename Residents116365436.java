
import java.io.IOException;

/*------CHOCO Library Imports----------*/

import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.nary.automata.FA.FiniteAutomaton;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.search.strategy.selectors.values.IntDomainMin;
//import org.chocosolver.solver.search.strategy.selectors.variables.ImpactBased;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.tools.ArrayUtils;

/*
 * Report
 * ------------------------------------------------------------------------------------------------------------------------
 * Name: Colm Clery
 * 
 * Student ID: 116365436
 * 
 * Description of problem:
 * A class for solving the issue of scheduling timetables for graduate doctors, who
 * are in the process of becoming fully qualified doctors. In order to become fully 
 * qualified, a doctor must take number of mandatory tutorials.
 * 
 * The trainee doctors are important for a functioning hospital
 * and they work a number of mandatory shifts to meet the requirement of having a 
 * certain amount of doctors present at each shift. Due to the long hours, a break must be scheduled
 * into the rota for each doctor to ensure the hospital doesn't overwork the doctors, 
 * according to the legal maximum.
 * 
 * My Implementation:
 * In my model, two IntVar matrixes are used and one IntVar array is used to store the data.  
 * My implementation uses sum and regular global constraints.
 * 
 * The first matrix "shiftsAssigned", stores a q x m matrix of 0/1, where shiftsAssigned[q][m] = 1 means resident q is working for shift m. I picked
 * an intVarMatrix to store this information as it allows for global constraints such as "sum" and "scalar" which
 * can be used to apply the constraint that each resident works a certain amount of shifts.
 * 
 * It also allowed for the use of the global constraint "regular" to ensure that each resident can't 
 * work for a sequence of more than the designated amount of shifts. This was done in my model by creating a finite
 * automata with the set of possible permutations of 1's(scheduled to work) and 0's(resting) given in the regular expression.
 * 
 * The IntVarMatrix of [resident][shift] also allowed for iteration through the matrix to get each IntVarArray of shifts, which
 * was used for adding regular expression, which stated that for each resident, a certain amount
 * of 0's in a row had to be present in order for each resident to received their break.
 * 
 * Finally, storing the data in this matrix allowed for addition of specific constraints. In the model, there were specific constraints
 * which specified that certain tutorials had to be attended during shifts. With this matrix it was possible to store 0 and 1 values to
 * ensure that each required tutorial was taken by residents.
 * 
 * The second matrix "staffAssigned", stores the transposed matrix of "shiftsAssigned", where 
 * shiftsAssigned[m][q] = 1 means that for shift m, resident q is working. This matrix was picked to ensure that for each time slot
 * the minimum number of staff per shift constraint could be met with the global constraint "sum". 
 * 
 * The "shiftsPerResident" IntVarArray stores total scheduled shifts for each resident. It contains a value for the amount of shifts scheduled
 * for each resident. This could then be used with the global constraint sum to ensure that the minimum amount of scheduled shifts possible 
 * was searched for in the Search strategy. 
 *  
 * The search strategy used in this model is domOverWDegSearch, as it is the search strategy used for Integer variables & 
 * Boolean variables in chocosolver, in which the ValueSelector is the IntDomainMin(). I picked this search strategy, because the purpose of the model is 
 * seeking the lowest amount of assigned shifts allowed. The domOverWDegSearch strategy assigns a variable to it's lower bound.
 * 
 * 
 * Results:
 * 
 * 	(A) The minimum amount of scheduled shifts possible, using my model for "residents0.txt":
 * 				
 *					Shifts
 *
 *					0 	1 	2 	3 	4 	5 	6 
 *	-----------------------------------------------------------------
 *	resident_0: 	1	1	0	1	1	0	0	
 *	resident_1: 	0	1	1	0	0	1	1	
 *	Total amount of shifts: 8
 *
 *  
 *  
 *  (B) The minimum amount of scheduled shifts possible, using my model for "residents1.txt":
 *  				
 *  				Shifts
 *
 *					0 	1 	2 	3 	4 	5 	6 
 *	-----------------------------------------------------------------
 *	resident_0: 	1	1	0	1	1	0	0	
 *	resident_1: 	0	0	1	0	0	1	1	
 *	resident_2: 	1	0	1	1	0	0	1
 *	Total amount of shifts: 11
 *  
 *  
 *  (C) The minimum amount of scheduled shifts possible, using my model for "residents2.txt":
 *  
 *  				Shifts
 *	
 *					0 	1 	2 	3 	4 	5 	6 	7 
 *	-------------------------------------------------------------------------
 *	resident_0: 	0	0	0	0	1	1	1	1	
 *	resident_1: 	1	1	1	1	0	0	0	0	
 *	resident_2: 	0	0	0	0	1	1	1	1	
 *	resident_3: 	1	1	1	1	0	0	0	0
 *	Total amount of shifts: 16
 *
 *
 *	(D) The minimum amount of scheduled shifts possible, using my model for "residents3.txt":
 *				
 *					Shifts
 *
 *					0 	1 	2 	3 	4 	5 	6 	7 	8 	9 	10 	11 	12 	13 	14 	15 	16 	17 	18 	19 	20 	21 	22 	23 	24 	25 	26 	27 
 *-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
 * resident_0: 		1	0	0	0	1	1	0	0	0	0	0	1	0	0	0	1	0	0	0	1	1	1	0	0	0	0	0	0	
 * resident_1: 		0	0	1	0	0	0	0	0	0	1	1	0	0	1	1	0	0	1	1	1	0	0	0	0	0	1	1	1	
 * resident_2: 		1	1	0	0	1	1	1	0	0	1	0	0	0	1	0	0	0	0	0	0	0	0	1	1	0	0	0	0	
 * resident_3: 		0	1	1	1	0	0	0	1	1	1	1	0	0	0	0	0	0	0	1	1	0	0	1	1	0	0	0	0	
 * resident_4: 		0	0	0	1	1	0	0	0	0	0	0	1	1	1	0	0	0	1	1	0	0	1	1	1	1	0	0	0	
 * resident_5: 		0	0	1	1	1	0	0	1	0	0	0	1	1	0	0	0	1	1	0	0	0	0	0	0	1	0	0	0	
 * resident_6: 		0	0	0	0	0	0	1	0	0	0	1	0	0	1	1	0	0	0	1	1	1	0	0	1	0	0	0	0	
 * resident_7: 		0	0	1	0	0	1	1	1	0	0	0	0	0	0	1	1	0	0	0	0	0	1	0	0	0	1	1	1	
 * resident_8: 		0	1	0	0	0	1	1	1	0	0	0	0	0	0	1	1	1	1	0	0	0	1	0	0	0	1	1	1	
 * resident_9: 		0	1	1	1	1	0	0	0	1	1	1	1	0	0	0	1	0	0	0	0	0	0	1	0	0	1	1	1	
 * Total amount of shifts: 102
 *
 *
 *	(E) The minimum amount of scheduled shifts possible, using my model for "residents4.txt":
 *				
 *					Shifts
 *
 *					0 	1 	2 	3 	4 	5 	6 	7 	8 	9 	10 	11 	12 	13 	14 	15 	16 	17 	18 	19 	20 	21 	22 	23 	24 	25 	26 	27 
 * -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
 * resident_0: 		1	0	0	0	1	1	0	0	0	1	1	1	0	0	0	1	0	0	0	1	1	1	0	0	0	0	0	0	
 * resident_1: 		0	0	1	0	0	0	0	0	0	0	0	1	1	1	1	0	0	1	1	1	0	0	0	0	0	1	1	1	
 * resident_2: 		1	1	0	0	1	1	1	0	0	1	0	0	1	1	0	0	0	0	0	0	0	0	1	1	0	0	0	0	
 * resident_3: 		0	1	1	0	0	0	0	1	1	1	1	0	0	0	0	0	0	0	1	1	0	0	1	1	0	0	0	0	
 * resident_4: 		0	0	0	1	1	0	0	0	0	0	0	1	0	0	0	1	1	1	0	0	0	1	1	1	1	0	0	0	
 * resident_5: 		0	0	1	1	1	1	0	0	1	1	0	0	0	0	0	0	1	1	1	0	0	0	0	0	1	0	0	0	
 * resident_6: 		0	1	1	1	0	0	1	0	0	0	0	0	0	1	1	0	0	0	1	1	1	0	0	1	0	0	0	0	
 * resident_7: 		0	0	1	0	0	1	1	1	0	0	0	0	0	0	1	1	0	0	0	0	0	1	0	0	0	1	1	1	
 * resident_8: 		0	0	0	0	0	0	1	1	0	0	1	0	0	1	1	0	0	1	0	0	0	1	0	0	0	1	1	1	
 * resident_9: 		0	1	1	1	1	0	0	1	0	0	1	1	0	0	0	1	0	0	0	0	0	0	1	0	0	1	1	1	
 * Total amount of shifts: 103
 *   
 *
 * 
 * 
 *  Timings For "Residents0.txt":
 * --------------------------------------------------------------------------------------------------------------------------
 * |   Search Strategy						|	Building Time						|   Resolution Time					    |
 * |										|										|										|
 * -------------------------------------------------------------------------------------------------------------------------
 * |										|										|										|
 * |	Default								|	0.349s								|	0.025s								|
 * |										|										|										|
 * --------------------------------------------------------------------------------------------------------------------------	
 * |										|										|										|
 * |	domOverWDegSearch					|	0.200s								|	0.012s								|
 * |										|										|										|
 * --------------------------------------------------------------------------------------------------------------------------	
 * |										|										|										|
 * |	inputOrderLBSearch					|	0.279s								|	0.016s								|
 * |										|										|										|
 * --------------------------------------------------------------------------------------------------------------------------	
 * |										|										|										|
 * |	activityBasedSearch					|	0.310s								|	0.019s								|
 * |										|										|										|
 * --------------------------------------------------------------------------------------------------------------------------	
 * |										|										|										|
 * |	ImpactBased	Search					|	0.316s								|	0.016s								|
 * |										|										|										|
 * --------------------------------------------------------------------------------------------------------------------------
 * 
 */



public class Residents116365436 {
	public static void main(String[] args) throws IOException {
		ResidentsReader data = new ResidentsReader("src/data/residents0.txt");	
		/* 
		 *  Test Files:
		 */
		 //ResidentsReader data = new ResidentsReader("src/data/residents4.txt");
		 //ResidentsReader data = new ResidentsReader("src/data/residents3.txt");
		 //ResidentsReader data = new ResidentsReader("src/data/residents2.txt");
		 //ResidentsReader data = new ResidentsReader("src/data/residents1.txt");
	
		int numResidents = data.getNumResidents(); 				// total number of residents-n
		int numShifts = data.getNumShifts();                    // total number of shifts-m
		int numQualifications = data.getNumQuals(); 			// total number of qualifications offered-q
		int[] minStaffForShift = data.getMinResidents(); 		// array of size m-min staff for each shift 
		int[][] qualificationsOffered = data.getQualsOffered(); // a qxm matrix of 0/1, where qualsOffered[i][j] means qual 
																// i offered on shift j 							
		int[][] qualificationsNeeded = data.getQualsNeeded();   // a nxq matrix of 0/1, where qualsNeeded[k][i] means 
																// resident k needs qual i
		int maxBlock = data.getMaxBlock(); 						// the maximum length of a block of shifts
		int restPeriod = data.getRestPeriod(); 					// minimum free shifts required between blocks
		int breakPeriod = data.getBreakPeriod();				// must be a sequence of free shifts this long
		int minShifts = data.getMinShifts(); 					// minimum shifts to be scheduled per resident
		
		String breakToBeAdded = "";								// will store the break period that must be given to staff
	    String maxToBeAdded = "";								// will store a FA representing the maximum number of 1's that can appear together
	    String restSession = "";								// will store a FA for how long the rest period between shifts has to be
	    String overallRegularExpression = "((<0>|";				// will store a FA for the possible combinations of breaks and shifts in 1's and 0's
	    String overallEnding = "(<0>|";							// will store a FA of the possible endings for the rota
		
	    /*------SOLVER---------------*/
		
		Model model = new Model("The Residents Scheduling Problem");
		
		/*------VARIABLES------------*/
		
		int maxShifts = numShifts*numResidents; 											// Maximum possible number of shifts assigned
	    IntVar totalNumberOfShifts = model.intVar(0, maxShifts);							// The sum of all shifts assigned.
		IntVar shiftsAssigned[][] = model.intVarMatrix(numResidents,  numShifts, 0, 1); 	// A matrix of [residents][shift] with a boolean value of 0/1
		IntVar shiftsPerResident [] = model.intVarArray(numResidents, 0, numShifts);		// Contains the sum of the total number of shifts per resident
		
		/*------CONSTRAINTS----------*/
		
		/*
		 *  Part 1 of assignment:
		 *  
		 *  Constraint 1: Adding constraint that each resident must take at least one tutorial of the required type they need to qualify
		 */ 	
		
	    for (int resident = 0; resident < numResidents; resident++) {
	    	for (int qualification = 0; qualification < numQualifications; qualification++) {
	    		if (qualificationsNeeded[resident][qualification] == 1) {
	    			for (int qualificationTime = 0; qualificationTime < numShifts; qualificationTime++) {
	    				if (qualificationsOffered[qualification][qualificationTime]==1) {
	    					model.arithm(shiftsAssigned[resident][qualificationTime], "=", 1).post();
	    					break; //Only one tutorial needs to be attended.
	    				}			
	    			}
	    		}
	    	}
	    }
	    
	    /*
		 *  Constraint 2: Each resident works a minimum number of shifts.
		 */ 	
	    
	    for (int resident = 0; resident<numResidents; resident++) {
	        model.sum(shiftsAssigned[resident], ">=", minShifts).post();
	        model.sum(shiftsAssigned[resident],"=", shiftsPerResident[resident]).post(); // Storing the sum of each resident row, to calculate the overall scheduled shifts
	    }
	    
	    /*
		 * Constraint 3: Adding constraint that there should be a minimum number of staff per shift.
		 */ 	
	    
	    IntVar staffAssigned[][] = ArrayUtils.transpose(shiftsAssigned);
	    for (int shift = 0; shift<numShifts; shift++) {
	        model.sum(staffAssigned[shift], ">=", minStaffForShift[shift]).post();  
	    }
	    
	    /* 
	     * Part 2 of assignment: 
	     * 
	     * Adding Constraint for a maximum block of shifts
	     */
	    
	    for (int i=0; i<=breakPeriod-1;i++) {			  // constructing a finite automata of the break period required
	    	breakToBeAdded = breakToBeAdded + "<0>";
	    }
	    String breakRegularExpression = "((<0>|<1>)*" + breakToBeAdded + "(<0>|<1>)*)";
	    for (int i=0; i<=restPeriod-1;i++) {			  // constructing a finite automata representing the rest period between shifts
	    	restSession = restSession + "<0>";
	    }
	    for (int i=0; i<=maxBlock-1;i++) {				  // constructing a finite automata representing the set of possible permutations of 1's and 0's that must be met 		
	    	maxToBeAdded = maxToBeAdded + "<1>";
	    	overallEnding = overallEnding + maxToBeAdded;
	    	overallRegularExpression = overallRegularExpression  + maxToBeAdded + restSession;
	    	if (!(maxBlock == i+1)){
	    		overallRegularExpression = overallRegularExpression + "|";
	    		overallEnding = overallEnding + "|";
	    	}
	    	else {
	    		overallRegularExpression = overallRegularExpression + ")*)";
	    		overallEnding = overallEnding + ")";
	    	}
	    }

	    FiniteAutomaton shiftsAvailable = new FiniteAutomaton(overallRegularExpression+overallEnding);	// Enabling an ending of 1's 
	    FiniteAutomaton brakeToTake = new FiniteAutomaton(breakRegularExpression);
	    for(int resident=0; resident< numResidents; resident++) { 		// Post the regular expressions for each row.
	    	model.regular(shiftsAssigned[resident],brakeToTake).post(); 
		    model.regular(shiftsAssigned[resident],shiftsAvailable).post();
	    }
	    IntVar[] searchVars1 = ArrayUtils.flatten(staffAssigned);
	    model.sum(shiftsPerResident, "=", totalNumberOfShifts).post();	// Assigning totalNumberOfShifts equal to the sum of all column sums
	    Solver solver = model.getSolver();
		model.setObjective(Model.MINIMIZE, totalNumberOfShifts);
	    
		/*------SEARCH STRATEGY-------*/
		
		solver.setSearch(Search.domOverWDegSearch(searchVars1));
		//solver.setSearch(Search.minDomLBSearch(searchVars1));
		//solver.setSearch(Search.inputOrderUBSearch(searchVars1));
		//solver.setSearch(Search.inputOrderLBSearch(searchVars1));
		//solver.setSearch(Search.activityBasedSearch(searchVars1)); 		 
		//solver.setSearch(new ImpactBased(searchVars1, true));

		/*------SOLUTION-------------*/
		
		while (solver.solve()) { //print the solution
			System.out.println("\nSolution " + solver.getSolutionCount() + ":");
			System.out.println("				Shifts\n");
			System.out.print("	");
			var lengthOfBar = "---------";
			for (int t = 0; t < numShifts; t++) {
				System.out.print("	" + t + " ");
				lengthOfBar = lengthOfBar + "--------";
			}
			System.out.print("\n");
			System.out.println(lengthOfBar);
			for (int residents = 0; residents < numResidents; residents++) { // Number of residents
				System.out.print("resident_"+residents + ": 	");	            
				for(int shiftNum =0; shiftNum < numShifts; shiftNum++) {
					System.out.print( shiftsAssigned[residents][shiftNum].getValue() + "	");	
				}
				System.out.print("\n");
			}
			System.out.print("Total amount of shifts: "+totalNumberOfShifts.getValue() + "\n   ");
			
		}
		solver.printStatistics();
		System.out.println("Residents116365436.java.");
		
		}	
		
}
