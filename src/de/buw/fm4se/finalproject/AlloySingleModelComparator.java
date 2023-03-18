package de.buw.fm4se.finalproject;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.ExprVar;
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

//			int number = world.getAllFunc().size();
//			System.out.println("Number of facts: " + number);
//			if (number == 1) {
//				for (Pair<String, Expr> fact : world.getAllFacts()) {
//					System.out.println(fact.toString());
//				}
//			}else if (number > 1) {
//				for (Func func : world.getAllFunc()) {
//					String baseName = func.label.substring(func.label.indexOf("/") + 1);
//					if (baseName.endsWith("ALT")) {
//						altPredicates.put(baseName.substring(0, baseName.length() - 3), func);
//					} else {
//						predicates.put(baseName, func);
//					}
//				}
//			}

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
					if (altPred.getKey().contains(pred.getKey())) {
						String semanticallyEqual = comparePredicates(world, stringAlloyModel, pred.getValue().label,
								altPred.getValue().label, options, reporter);
						System.out.println("Comparison of " + pred.getValue().label + " and " + altPred.getValue().label
								+ " : " + semanticallyEqual);
						if (semanticallyEqual.equals("equivalent")) {
							System.out.println(
									"For extension comparisons you can create a predicate in you alloy model like this : pred P_and_Q_extension {"
											+ pred.getValue().label + "  and not  " + altPred.getValue().label + "}");
							System.out.println(
									"Or if you prefer evaluate refinement you can create this one: pred P_and_Q_refinement {"
											+ altPred.getValue().label + "  and not  " + pred.getValue().label + "}");
						} else if (semanticallyEqual.equals("extension")) {
							System.out.println(
									"For refinement comparision you can create this one: pred P_and_Q_refinement {"
											+ altPred.getValue().label + "  and not  " + pred.getValue().label + "}");
						} else if (semanticallyEqual.equals("refined")) {
							System.out.println(
									"For extension comparisons you can create a predicate in you alloy model like this : pred P_and_Q_extension {"
											+ pred.getValue().label + "  and not  " + altPred.getValue().label + "}");
						} else {
							System.out.println("Comparision between: " + pred.getValue().label + " and "
									+ altPred.getValue().label + " is Incomparable");
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
			return "equivalent";
		} else if (!ansExtension.satisfiable()) {
			return "extension";
		} else if (!ansRefinement.satisfiable()) {
			return "refined";
		} else {
			return "Incomparable";
		}
	}
	
	public static String compareFacts(Module world, String stringAlloyModel, String factName1, String factName2, A4Options options, A4Reporter reporter) throws Err {
	    String sigName = findCommonSig(world, factName1, factName2);
	    if (sigName == null) {
	        return "Incomparable (no common signature)";
	    }

	    String newModuleString = stringAlloyModel +
	        "\npred newCombinedFact[a: " + sigName + "] {\n" +
	        "    " + factName1 + "[a] <=> " + factName2 + "[a]\n" +
	        "}\n" +
	        "run newCombinedFact for 3";

	    Module newWorld = CompUtil.parseOneModule_fromString(reporter, newModuleString);
	    Command newCmd = new Command(false, 3, 3, 3, "newCombinedFact");
	    A4Solution sol = TranslateAlloyToKodkod.execute_command(reporter, newWorld.getAllReachableSigs(), newCmd, options);

	    if (sol.satisfiable()) {
	        return "Equivalent";
	    }

	    String newModuleString2 = stringAlloyModel +
	        "\npred newCombinedFact2[a: " + sigName + "] {\n" +
	        "    " + factName1 + "[a] => " + factName2 + "[a]\n" +
	        "}\n" +
	        "run newCombinedFact2 for 3";

	    Module newWorld2 = CompUtil.parseOneModule_fromString(reporter, newModuleString2);
	    Command newCmd2 = new Command(false, 3, 3, 3, "newCombinedFact2");
	    A4Solution sol2 = TranslateAlloyToKodkod.execute_command(reporter, newWorld2.getAllReachableSigs(), newCmd2, options);

	    if (sol2.satisfiable()) {
	        return factName1 + " refines " + factName2;
	    }

	    String newModuleString3 = stringAlloyModel +
	        "\npred newCombinedFact3[a: " + sigName + "] {\n" +
	        "    " + factName2 + "[a] => " + factName1 + "[a]\n" +
	        "}\n" +
	        "run newCombinedFact3 for 3";

	    Module newWorld3 = CompUtil.parseOneModule_fromString(reporter, newModuleString3);
	    Command newCmd3 = new Command(false, 3, 3, 3, "newCombinedFact3");
	    A4Solution sol3 = TranslateAlloyToKodkod.execute_command(reporter, newWorld3.getAllReachableSigs(), newCmd3, options);

	    if (sol3.satisfiable()) {
	        return factName2 + " refines " + factName1;
	    }

	    return "Incomparable";
	}
	
	
	public static String findCommonSig(Module world, String factOrPredicateName1, String factOrPredicateName2) {
	    Set<String> sigs1 = new HashSet<>();
	    Set<String> sigs2 = new HashSet<>();

	    // Find the signatures used in the first fact or predicate
	    for (Func func : world.getAllFunc()) {
	        if (func.label.equals(factOrPredicateName1)) {
	            for (ExprVar param : func.decls.get(0).names) {
	                sigs1.add(param.type().toString());
	            }
	            break;
	        }
	    }

	    // Find the signatures used in the second fact or predicate
	    for (Func func : world.getAllFunc()) {
	        if (func.label.equals(factOrPredicateName2)) {
	            for (ExprVar param : func.decls.get(0).names) {
	                sigs2.add(param.type().toString());
	            }
	            break;
	        }
	    }

	    // Find the common signature
	    for (String sig1 : sigs1) {
	        if (sigs2.contains(sig1)) {
	            return sig1;
	        }
	    }

	    return null;
	}

	
	
}
