import java.io.IOException;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.variables.IntVar;

/*
 *  Pioneer Landing pathFinder
 *  Given an inventory of items, where each item has a scientific value, 
 *  a time required and a maximum amount of experiments that can be run,
 *  decide how many experiments of each type it should run, 
 *  to maximise the total sum of value from the individual experiments.
 *  
 *  
 *  uses the global constraint "knapsack"
 *  
 *  Data is read in from file, where the file must contain a series of n lines(ti   vi   mi), 
 *  where ti is the time required for an experiment of type i,
 *  vi is the scientific value of experiments of type i, 
 *  and mi is the maximum number of experiments of type i possible in this location
 *  n	t	b
 *  t0	v0	m0
 *  t1	v1 	m1
 *  ...
 *  t(n-1)	v(n-1)	m(n-1)
 *  e00 e01
 *  e10	e11
 *  ...
 *  e(b-1)0	e(b-1)1
 *  etc 
 */


public class Pioneer116365436{
	public static void main(String[] args) throws IOException {
		Model model = new Model("The Pioneer lander Problem");
		//PioneerData data = new PioneerData("src/data/pioneer0.txt");// For testing on pioneer0.txt	
		//PioneerData data = new PioneerData("src/data/pioneer1.txt");// For testing on pioneer1.txt	
		PioneerData data = new PioneerData("src/data/pioneer2.txt");// For testing on pioneer2.txt	
		int numTypes = data.getNumTypes(); //the number of experiment types
		int totalHours = data.getTotalHours(); // The total time available for experiments
		int numBefores = data.getNumBefores();// The total number of restrictions
		int[] hours = data.getHours(); // The hours for the experiments
		int[] values = data.getValues(); // The scientific values for the experiments
		int[] total =   data.getTotals(); // The total amount of times it is possible to carry out experiment
		int[][] befores =   data.getBefores(); // The experiments for which there is a relationship
		int maxValue = data.getMaxValues(); // The total value for all experiments.
		
		IntVar[] experiments = new IntVar[numTypes];
		for (int type = 0; type<numTypes; type++) {
			experiments[type] = model.intVar("experiments"+type, 0,  total[type]); // how many of each experiment type
		}
		
		// Creating variables
		IntVar totalTime = model.intVar("total time", 0, totalHours);    // The total time for selected experiments
		IntVar scientificValue = model.intVar("scientific value", 0, maxValue); //The total scientific value of selected items
		
		// Modelling the problem using a 'knapsack' constraint using the scientific value as "weight"
		model.knapsack(experiments, totalTime, scientificValue, hours, values).post();
		Solver solver = model.getSolver(); // solving the problem
		
		// Note - Using the default search strategy	

		for (int i = 0; i<numBefores; i++) { // Iterate through all the restrictions on pairs of experiments
			// Such constraint states that if v0 takes a value equal to 0 then the domain of the second element of the pair should 
			// be reduced to the domain of the first element. 
			// Hence, there should not be more experiments of the second type than the first type.
			Constraint c1 = model.arithm(experiments[befores[i][1]], "<=", experiments[befores[i][0]]);
			IntVar v0 = model.intVar("v0", 0);
			Constraint c2 = model.arithm(v0, "=", 0);
			model.ifThen(c2, c1);	      	 
		}	
		
		// States that the experiment's value is to be maximised
		model.setObjective(Model.MAXIMIZE, scientificValue);
		
		int numsolutions = 0;
		while (solver.solve()) { 
			numsolutions++;
			System.out.println("Solution " + numsolutions + ":  --------------------------------------");
			// Next code block interrogates the variables and gets the current solution
			System.out.print("types:   ");
			for (int type = 0; type<numTypes; type++) {
				System.out.print("\t" + type);
			}
			System.out.println();
			System.out.print("experiments:   ");
			for (int type = 0; type<numTypes; type++) {
				System.out.print("\t" + experiments[type].getValue());
			}
			System.out.println( "\n\ntotal time= " + totalTime.getValue());
			System.out.println("Scientific Value= " + scientificValue.getValue() + "\n");
		}
	    // Note - last solution generated is the optimal one
		solver.printStatistics(); 	
	}	
}
