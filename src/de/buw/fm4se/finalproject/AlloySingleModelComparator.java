package de.buw.fm4se.finalproject;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.nio.file.Files;
import java.nio.file.Paths;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class AlloySingleModelComparator {

	public static void main(String[] args) {
		// Provide the path to the Alloy file as a command-line argument
		if (args.length != 1) {
			System.err.println("Usage: AlloySingleModelComparator <model_path>");
			return;
		}

		String modelPath = args[0];

		A4Reporter reporter = new A4Reporter() {
			@Override
			public void warning(ErrorWarning msg) {
				System.out.println("Warning: " + msg);
			}
		};

		try {
			// Load the Alloy model from the file
			Module world = CompUtil.parseEverything_fromFile(reporter, null, modelPath);

			String stringAlloyModel = new String(Files.readAllBytes(Paths.get(modelPath)));

			A4Options options = new A4Options();
			options.solver = A4Options.SatSolver.SAT4J;

			// Iterate through the facts or predicates in the model and identify the ones
			// that have the "ALT" suffix
			Map<String, Func> predicates = new HashMap<>();
			Map<String, Func> altPredicates = new HashMap<>();
			for (Func func : world.getAllFunc()) {
				String baseName = func.label.substring(func.label.indexOf("/") + 1);
				if (baseName.endsWith("ALT")) {
					altPredicates.put(baseName.substring(0, baseName.length() - 3), func);
				} else {
					predicates.put(baseName, func);
				}
			}

			for (Map.Entry<String, Func> pred : predicates.entrySet()) {
				for (Map.Entry<String, Func> altPred : altPredicates.entrySet()) {
//				if (altPredicates.containsKey(pred.getKey())) {
					if (altPred.getKey().contains(pred.getKey())) {
//					if ( pred.getKey().contains(altPred.getKey())   )  {
						// Perform semantic comparison and generate examples illustrating potential
						// differences
//						String semanticallyEqual = comparePredicates(world, pred.getValue().label, altPredicates.get(pred.getKey()).label, options, reporter);
						
						String predicate1Body = getPredicateBodyAsString(world, pred.getValue().label);
						printSignatureTypesInPredicateString(pred.getValue().label, predicate1Body);
						
						
						String semanticallyEqual = comparePredicates(world, stringAlloyModel, pred.getValue().label, altPred.getValue().label, options, reporter);
//						System.out.println("Comparison of " + pred.getValue().label + " and " + altPredicates.get(pred.getKey()).label + ":");
						System.out.println("  Semantically equal: " + semanticallyEqual);
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

//	private static boolean comparePredicates(Module world, String predName1, String predName2, A4Options options, A4Reporter reporter) throws Exception {
//	    // Generate a new predicate for comparing the predicates
//	    String comparePredicate = "pred comparison[a: univ, b: univ] {(" + predName1 + "[a, b] iff " + predName2 + "[a, b])}";
//
//	    // Generate a new command for running the comparison predicate
//	    String compareCommand = "run comparison for 3";
//
//	    // Create a separate module by appending the necessary comparison predicate and command to the original module as a string
//	    String newModuleString = world.toString() + "\n" + comparePredicate + "\n" + compareCommand;
//
//	    // Parse the entire module again
//	    Module newWorld = CompUtil.parseEverything_fromString(reporter, newModuleString);
//
//	    // Find the new command
//	    Command newCommand = newWorld.getAllCommands().get(newWorld.getAllCommands().size() - 1);
//
//	    // Execute the new command
//	    A4Solution ans = TranslateAlloyToKodkod.execute_command(reporter, newWorld.getAllSigs(), newCommand, options);
//
//	    // Return true if the predicates are semantically equal, false otherwise
//	    return ans.satisfiable() ? true : false;
//	}

	private static String comparePredicates(Module world, String stringAlloyModel, String predName1, String predName2,
			A4Options options, A4Reporter reporter) throws Exception {
		// Generate predicates for comparing the predicates
		String comparePredicate1 = "pred comparison1[a: univ, b: univ] {(" + predName1 + "[a, b] implies " + predName2
				+ "[a, b])}";
		String comparePredicate2 = "pred comparison2[a: univ, b: univ] {(" + predName2 + "[a, b] implies " + predName1
				+ "[a, b])}";

//		String type = world.

		String P_and_Q_equivalent = "all s: Person | not (someoneKilledAgatha iff someoneKilledAgatha_ALT)";

		// Generate commands for running the comparison predicates
		String compareCommand1 = "run comparison1 for 5";
		String compareCommand2 = "run comparison2 for 5";

		// Create a separate module by appending the necessary comparison predicates and
		// commands to the original module as a string

		String newModuleString = stringAlloyModel + "\n" + comparePredicate1 + "\n" + comparePredicate2 + "\n"
				+ compareCommand1 + "\n" + compareCommand2;

		// Parse the entire module again
		Module newWorld = CompUtil.parseEverything_fromString(reporter, newModuleString);

		// Find the new commands
		Command newCommand1 = newWorld.getAllCommands().get(newWorld.getAllCommands().size() - 2);
		Command newCommand2 = newWorld.getAllCommands().get(newWorld.getAllCommands().size() - 1);

		// Execute the new commands
		A4Solution ans1 = TranslateAlloyToKodkod.execute_command(reporter, newWorld.getAllSigs(), newCommand1, options);
		A4Solution ans2 = TranslateAlloyToKodkod.execute_command(reporter, newWorld.getAllSigs(), newCommand2, options);

		// Analyze the results and return the relationship between the two predicates or
		// facts
		if (ans1.satisfiable() && ans2.satisfiable()) {
			return "equivalent";
		} else if (ans1.satisfiable()) {
			return "refines";
		} else if (ans2.satisfiable()) {
			return "refined by";
		} else {
			return "incomparable";
		}
	}

	public static String getPredicateBodyAsString(Module module, String predicateName) {
		for (Func func : module.getAllFunc()) {
			if (func.isPred && func.label.endsWith("/" + predicateName)) {
				return func.getBody().toString();
			}
		}
		throw new RuntimeException("Predicate not found: " + predicateName);
	}

	public static void printSignatureTypesInPredicateString(String predicateName, String predicateBody) {
		Pattern pattern = Pattern.compile("([A-Za-z0-9_]+)\\[.*?\\]");
		Matcher matcher = pattern.matcher(predicateBody);
		Set<String> signatureTypes = new HashSet<>();

		while (matcher.find()) {
			signatureTypes.add(matcher.group(1));
		}

		System.out.println("Signature types in " + predicateName + ": " + signatureTypes);
	}

}
