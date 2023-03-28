package de.buw.fm4se.finalproject;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
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

			String alternativeModelPath = "./new_model.als";
//			String stringAlloyModel = new String(Files.readAllBytes(Paths.get(modelPath)));
			String stringAlloyModel = new String();

			A4Options options = new A4Options();
			options.solver = A4Options.SatSolver.SAT4J;

			// Iterate through the facts or predicates in the model and identify the ones
			// that have the "ALT" suffix
			Map<String, Object> predicatesOrFacts = new HashMap<>();
			Map<String, Object> altPredicatesOrFacts = new HashMap<>();

			int numPredicates = world.getAllFunc().size();
			int numFacts = world.getAllFacts().size();
			System.out.println("Number of Predicates: " + numPredicates);

			if (numPredicates == 1 && numFacts > 0) {
				world = changeFactsToPredicates(world, options, reporter, alternativeModelPath);
				stringAlloyModel = new String(Files.readAllBytes(Paths.get(alternativeModelPath)));
			} else {
				stringAlloyModel = new String(Files.readAllBytes(Paths.get(modelPath)));
			}

			int numNewPredicates = world.getAllFunc().size();

			if (numNewPredicates > 1) {
				for (Func func : world.getAllFunc()) {
					String baseName = func.label.substring(func.label.indexOf("/") + 1);
					if (baseName.endsWith("ALT")) {
//						altPredicatesOrFacts.put(baseName.substring(0, baseName.length() - 3), func);
						altPredicatesOrFacts.put(baseName, func);
					} else {
						predicatesOrFacts.put(baseName, func);
					}
				}
			} else {
				System.err.println("Can you please give a valid model.");
				return;
			}

			for (Map.Entry<String, Object> predFact : predicatesOrFacts.entrySet()) {
				for (Map.Entry<String, Object> altPredFact : altPredicatesOrFacts.entrySet()) {
					if (altPredFact.getKey().contains(predFact.getKey())) {

//						String predOrFact = predFact.getValue().toString();
//						String altPredOrFact = altPredFact.getValue().toString();

						String predOrFact = predFact.getKey().toString();
						String altPredOrFact = altPredFact.getKey().toString();

						String semanticallyEqual = "";

						semanticallyEqual = comparePredicates(world, stringAlloyModel, predOrFact, altPredOrFact,
								options, reporter);

						System.out.println(
								"Comparison of " + predOrFact + " and " + altPredOrFact + " : " + semanticallyEqual);
						if (semanticallyEqual.equals("equivalent")) {
							System.out.println(
									"For extension comparisons you can create a predicate in you alloy model like this : pred P_and_Q_extension {"
											+ predOrFact + "  and not  " + altPredOrFact + "}");
							System.out.println(
									"Or if you prefer evaluate refinement you can create this one: pred P_and_Q_refinement {"
											+ altPredOrFact + "  and not  " + predOrFact + "}");
						} else if (semanticallyEqual.equals("extension")) {
							System.out.println(
									"For refinement comparision you can create this one: pred P_and_Q_refinement {"
											+ altPredOrFact + "  and not  " + predOrFact + "}");
						} else if (semanticallyEqual.equals("refined")) {
							System.out.println(
									"For extension comparisons you can create a predicate in you alloy model like this : pred P_and_Q_extension {"
											+ predOrFact + "  and not  " + altPredOrFact + "}");
						} else {
							System.out.println("Comparision between: " + predOrFact + " and " + altPredOrFact
									+ " is Incomparable");
						}
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private static String comparePredicates(Module world, String stringAlloyModel, String predName1, String predName2,
			A4Options options, A4Reporter reporter) throws Exception {
		// Generate predicates for comparing the predicates

		String P_and_Q_equivalent = "pred P_and_Q_equivalent { not ( " + predName1 + " iff " + predName2 + ")}";
		String P_and_R_extension = "pred P_and_Q_extension { " + predName1 + "  and not  " + predName2 + "}";
		String P_and_Q_refinement = "pred P_and_Q_refinement {" + predName2 + " and not " + predName1 + "}";

		// Generate commands for running the comparison predicates
		String equivalenceCommand = "run P_and_Q_equivalent for 10";
		String extensionCommand = "run P_and_Q_extension for 10";
		String refinementCommand = "run P_and_Q_refinement for 10";

		// Create a separate module by appending the necessary comparison predicates and
		// commands to the original module as a string

		String newModuleString = stringAlloyModel + "\n" + P_and_Q_equivalent + "\n" + P_and_R_extension + "\n"
				+ P_and_Q_refinement + "\n" + equivalenceCommand + "\n" + extensionCommand + "\n" + refinementCommand;

		// Parse the entire module again
		Module newWorld = CompUtil.parseEverything_fromString(reporter, newModuleString);

		// Find the new commands
		Command commandEquivalent = newWorld.getAllCommands().get(newWorld.getAllCommands().size() - 3);
		Command commandExtension = newWorld.getAllCommands().get(newWorld.getAllCommands().size() - 2);
		Command commandRefinement = newWorld.getAllCommands().get(newWorld.getAllCommands().size() - 1);

		// Execute the new commands
		A4Solution ansEquivalent = TranslateAlloyToKodkod.execute_command(reporter, newWorld.getAllSigs(),
				commandEquivalent, options);
		A4Solution ansExtension = TranslateAlloyToKodkod.execute_command(reporter, newWorld.getAllSigs(),
				commandExtension, options);
		A4Solution ansRefinement = TranslateAlloyToKodkod.execute_command(reporter, newWorld.getAllSigs(),
				commandRefinement, options);

		// Analyze the results and return the relationship between the two predicates or
		// facts
		if (!ansEquivalent.satisfiable()) {
			return "Equivalent";
		} else if (!ansExtension.satisfiable()) {
			return "Extension";
		} else if (!ansRefinement.satisfiable()) {
			return "Refined";
		} else {
			return "Incomparable";
		}
	}

	private static Module changeFactsToPredicates(Module world, A4Options options, A4Reporter reporter,
			String outputFilePath) throws Exception {

//		String outputFilePath = "./new_model.als";
		SafeList<Sig> signatures = world.getAllSigs();
		SafeList<Pair<String, Expr>> facts = world.getAllFacts();
		SafeList<Func> newPreds = new SafeList<>();

		for (Pair<String, Expr> fact : facts) {
			String factName = "pred_" + fact.a;
			Expr factExpr = fact.b;
			Func newPred = new Func(null, factName, null, factExpr, factExpr);
			newPreds.add(newPred);
		}

		StringBuilder newModel = new StringBuilder();

		if (signatures.size() > 0) {
			for (Sig sig : signatures) {
				newModel.append(sig.explain().toString()).append("\n");
			}
		}

		if (newPreds.size() > 0) {
			for (Func newfunc : newPreds) {
				newModel.append("pred " + newfunc.label + " { " + newfunc.getBody() + " } \n");
			}
		}

		String genericRun = "run {} for 3 \n";
		newModel.append(genericRun);

		Files.write(Paths.get(outputFilePath), newModel.toString().getBytes());
		System.out.println("Output file created: " + outputFilePath);

		Module newWorld = CompUtil.parseEverything_fromFile(reporter, null, outputFilePath);

		return newWorld;
	}
}