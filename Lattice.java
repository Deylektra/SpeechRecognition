import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Scanner;
import java.util.Stack;

/* 
Julianne and Erin
CS 241 Paired Programming Assignment
*/

public class Lattice {
	private String utteranceID; // A unique ID for the sentence
	private int startIdx, endIdx; // Indices of the special start and end tokens
	private int numNodes, numEdges; // The number of nodes and edges, respectively
	private Edge[][] adjMatrix; // Adjacency matrix representing the lattice
								// Two dimensional array of Edge objects
								// adjMatrix[i][j] == null means no edge (i,j)
	private double[] nodeTimes; // Stores the timestamp for each node

	// Constructor

	// Lattice
	// Preconditions:
	// - latticeFilename contains the path of a valid lattice file
	// Post-conditions
	// - Field id is set to the lattice's ID
	// - Field startIdx contains the node number for the start node
	// - Field endIdx contains the node number for the end node
	// - Field numNodes contains the number of nodes in the lattice
	// - Field numEdges contains the number of edges in the lattice
	// - Field adjMatrix encodes the edges in the lattice:
	// If an edge exists from node i to node j, adjMatrix[i][j] contains
	// the address of an Edge object, which itself contains
	// 1) The edge's label (word)
	// 2) The edge's acoustic model score (amScore)
	// 3) The edge's language model score (lmScore)

	public Lattice(String latticeFilename) {
		String[][] latticeEntries = readFile(latticeFilename);
		parseFileHeader(latticeEntries);

		this.adjMatrix = parseEdges(latticeEntries);
		this.nodeTimes = parseNodeTimes(latticeEntries);

		return;
	}

	// Accessors

	// getUtteranceID
	// Pre-conditions:
	// - None
	// Post-conditions:
	// - Returns the utterance ID
	public String getUtteranceID() {
		return utteranceID;
	}

	// getNumNodes
	// Pre-conditions:
	// - None
	// Post-conditions:
	// - Returns the number of nodes in the lattice
	public int getNumNodes() {
		return numNodes;
	}

	// getNumEdges
	// Pre-conditions:
	// - None
	// Post-conditions:
	// - Returns the number of edges in the lattice
	public int getNumEdges() {
		return numEdges;
	}

	// toString
	// Pre-conditions:
	// - None
	// Post-conditions:
	// - Constructs and returns a string describing the lattice in the same
	// format as the input files. Nodes should be sorted ascending by node
	// index, edges should be sorted primarily by start node index, and
	// secondarily by end node index

	public String toString() {

		StringBuilder string = new StringBuilder("id " + utteranceID + "\n" + "start " + startIdx + "\n" + "end "
				+ endIdx + "\n" + "numNodes " + numNodes + "\n" + "numEdges " + numEdges + "\n");

		for (int i = 0; i < nodeTimes.length; i++) {
			string.append("node " + i + " " + nodeTimes[i] + "\n");
		}

		for (int i = 0; i < adjMatrix.length; i++) {
			for (int j = i; j < adjMatrix.length - 1; j++) {
				if (adjMatrix[i][j] != null) {
					string.append("edge " + i + " " + j + " " + adjMatrix[i][j].getLabel() + " "
							+ adjMatrix[i][j].getAmScore() + " " + adjMatrix[i][j].getLmScore() + "\n");
				}
			}
		}
		return string.toString();
	}

	// decode
	// Pre-conditions:
	// - lmScale specifies how much lmScore should be weighted
	// the overall weight for an edge is amScore + lmScale * lmScore
	// Post-conditions:
	// - A new Hypothesis object is returned that contains the shortest path
	// (aka most probable path) from the startIdx to the endIdx

	public Hypothesis decode(double lmScale) {
		Stack<Integer> result = new Stack<>();
		
		double[] cost = new double[numNodes];
		int[] parent = new int[numNodes];

		for (int i = 0; i < numNodes; i++) {
			cost[i] = java.lang.Double.POSITIVE_INFINITY;
		}
		cost[startIdx] = 0;

		int[] topSorted = topologicalSort();

		for (int n = 0; n < topSorted.length; n++) {
			int node = topSorted[n];
			for (int i = 0; i < numNodes; i++) {
				if (adjMatrix[i][node] != null
						&& (adjMatrix[i][node].getCombinedScore(lmScale) + cost[i]) < cost[node]) {
					cost[node] = adjMatrix[i][node].getCombinedScore(lmScale) + cost[i];
					parent[node] = i;
				}
			}
		}

		int node = endIdx;

		Hypothesis hypothesis = new Hypothesis();

		while (node != startIdx) {
			result.push(node);
			node = parent[node];
		}

		int stackSize = result.size();

		for (int n = 0; n < stackSize - 1; n++) {
			int i = result.pop();
			int j = result.peek();
			hypothesis.addWord(adjMatrix[i][j].getLabel(), adjMatrix[i][j].getCombinedScore(lmScale));
		}

		return hypothesis;
	}

	// topologicalSort
	// Pre-conditions:
	// - None
	// Post-conditions:
	// - A new int[] is returned with a topological sort of the nodes
	// For example, the 0'th element of the returned array has no
	// incoming edges. More generally, the node in the i'th element
	// has no incoming edges from nodes in the i+1'th or later elements

	public int[] topologicalSort() {
		int[] inDegrees = findInDegrees(adjMatrix);
		ArrayList<Integer> S = new ArrayList<Integer>();
		ArrayList<Integer> result = new ArrayList<Integer>();
		int[] topSorted = new int[numNodes];

		for (int i = 0; i < inDegrees.length; i++) {
			if (inDegrees[i] == 0) {
				S.add(inDegrees[i]);
			}
		}

		int n = 0;

		while (!S.isEmpty()) {
			n = S.remove(0);
			result.add(n);

			for (int b = 1; b < inDegrees.length; b++) {
				if (adjMatrix[n][b] != null && inDegrees[b] != 0) {
					inDegrees[b]--;
					if (inDegrees[b] == 0) {
						S.add(b);
					}
				}
			}
		}

		for (int i = 0; i < result.size(); i++) {
			topSorted[i] = result.get(i);
		}

		int sum = 0;
		for (int s = 0; s < numNodes; s++) {
			sum += inDegrees[s];
		}

		if (sum > 0) {
			System.out.print("Error: Graph has at least one cycle!");
			System.exit(0);
			return null; /// What are we supposed to put here?
		} else {
			return topSorted;
		}
	}

	// countAllPaths
	// Pre-conditions:
	// - None
	// Post-conditions:
	// - Returns the total number of distinct paths from startIdx to endIdx

	public java.math.BigInteger countAllPaths() {
		BigInteger[] count = new BigInteger[numNodes];
		ArrayList<LinkedList<Integer>> adjSet = createAdjSet();

		int[] topSorted = topologicalSort();

		for (int i = 0; i < numNodes; i++) {
			count[i] = BigInteger.ZERO;
		}

		count[startIdx] = BigInteger.ONE;
		for (int i = 0; i < numNodes - 1; i++) {
			int innerNode = topSorted[i];
			for (int j = 0; j < adjSet.get(innerNode).size(); j++) {
				int outerNode = adjSet.get(innerNode).get(j);
				count[outerNode] = count[outerNode].add(count[innerNode]);
			}
		}
		return count[endIdx];
	}

	// getLatticeDensity
	// Pre-conditions:
	// - None
	// Post-conditions:
	// - Returns the lattice density, which is defined to be:
	// (# of non -silence- words in lattice) / (# seconds from start to end index)
	public double getLatticeDensity() {
		double numNonSilence = 0.0;
		double numSeconds = nodeTimes[nodeTimes.length - 1] - nodeTimes[0];

		for (int i = 0; i < adjMatrix.length; i++) {
			for (int j = 0; j < adjMatrix.length; j++) {
				if (adjMatrix[i][j] != null && !adjMatrix[i][j].getLabel().equals("-silence-")) {
					numNonSilence++;
				}
			}
		}
		return numNonSilence / numSeconds;
	}

	// writeAsDot 
	// Pre-conditions:
	// - dotFilename is the name of the intended output file
	// Post-conditions:
	// - The lattice is written in the specified dot format to dotFilename
	public void writeAsDot(String dotFilename) {
		File file = new File(dotFilename);

		try {
			file.createNewFile();
		} catch (IOException e) {
			System.out.println("Unable to create file " + dotFilename);
		}

		try {
			FileWriter writer = new FileWriter(file);
			writer.write(toDot());
			writer.close();
		} catch (IOException e) {
			System.out.println("Unable to write to file " + dotFilename);
		}
		return;
	}

	// toDot - create a string in dot format
	// Pre-conditions:
	// - none
	// Post-conditions:
	// - The lattice is written in the specified dot format and returned to writeAsDot
	public String toDot() {
		StringBuilder string = new StringBuilder("digraph g  {\n" + "\trankdir=\"LR\"\n");
		for (int i = 0; i < numNodes; i++) {
			for (int j = 0; j < numNodes; j++) {
				if (adjMatrix[i][j] != null) {
					string.append("\t" + i + " -> " + j + " [label = \"" + adjMatrix[i][j].getLabel() + "\"]\n");
				}
			}
		}
		string.append("}");
		return string.toString();
	}

	// saveAsFile
	// Pre-conditions:
	// - latticeOutputFilename is the name of the intended output file
	// Post-conditions:
	// - The lattice's toString() representation is written to the output file

	public void saveAsFile(String latticeOutputFilename) {
		File file = new File(latticeOutputFilename);

		try {
			file.createNewFile();
		} catch (IOException e) {
			System.out.println("Unable to create file " + latticeOutputFilename);
		}

		try {
			FileWriter writer = new FileWriter(file);
			writer.write(toString());

			writer.close();
		} catch (IOException e) {
			System.out.println("Unable to write to file " + latticeOutputFilename);
		}
		return;
	}

	// uniqueWordsAtTime 
	// Pre-conditions:
	// - time is the time you want to query
	// Post-conditions:
	// - A HashSet is returned containing all unique words that overlap
	// with the specified time
	// (If the time is not within the time range of the lattice, the Hashset should
	// be empty)
	public java.util.HashSet<String> uniqueWordsAtTime(double time) {
		HashSet<String> uniqueWords = new HashSet<String>();
		for (int i = 0; i < numNodes; i++) {
			for (int j = 0; j < numNodes; j++) {
				if (adjMatrix[i][j] != null && nodeTimes[i] <= time && time <= nodeTimes[j]) {
					if (!uniqueWords.contains(adjMatrix[i][j].getLabel())) {
						uniqueWords.add(adjMatrix[i][j].getLabel());
					}
				}

			}
		}
		return uniqueWords;
	}

	// printSortedHits
	// Pre-conditions:
	// - word is the word (or multiword) that you want to find in the lattice
	// Post-conditions:
	// - The midpoint (halfway between start and end time) for each instance of word
	// in the lattice is printed to two decimal places in sorted (ascending) order
	// All times should be printed on the same line, separated by a single space
	// character
	// (If no instances appear, nothing is printed)

	public void printSortedHits(String word) {
		List<Double> times = new ArrayList<>();

		for (int i = 0; i < numNodes; i++) {
			for (int j = 0; j < numNodes; j++) {
				if (adjMatrix[i][j] != null && adjMatrix[i][j].getLabel().equals(word)) {
					double midpoint = (nodeTimes[j] + nodeTimes[i]) / 2;
					times.add(midpoint);
				}
			}
		}
		if (!times.isEmpty()) {
			Collections.sort(times);
			for (int i = 0; i < times.size(); i++) {
				System.out.printf("%.2f ", times.get(i));
			}
			System.out.printf("\n");
		}

	}

	// readFile 
	// Pre-conditions:
	// - latticeFilename is the name of the incoming lattice file
	// Post-conditions:
	// - The lattice is returned as an array, separated by line breaks
	public String[][] readFile(String latticeFilename) {
		File file = new File(latticeFilename);
		List<String> latticeEntries = new ArrayList<String>();
		Scanner scanner = null;

		try {
			scanner = new Scanner(file);
		} catch (FileNotFoundException e) {
			System.out.println("Error: Unable to open file " + latticeFilename);
			System.exit(1);
		} catch (NoSuchElementException e) {
			System.out.println("Error: Unable to parse file " + latticeFilename);
			System.exit(2);
		}

		while (scanner.hasNextLine()) {
			latticeEntries.add(scanner.nextLine());
		}

		Scanner entriesScanner = null;

		try {
			entriesScanner = new Scanner(file);
		} catch (FileNotFoundException e) {
			System.out.println("Error: Unable to open file " + latticeFilename);
			System.exit(1);
		} catch (NoSuchElementException e) {
			System.out.println("Error: Unable to parse file " + latticeFilename);
			System.exit(2);
		}

		String[][] latticeArray = new String[latticeEntries.size()][6];

		int i = 0;
		while (entriesScanner.hasNextLine()) {
			String line = entriesScanner.nextLine();
			String[] splitArray = line.split("\\s+");

			for (int j = 0; j < splitArray.length; j++) {
				latticeArray[i][j] = splitArray[j];
			}
			i++;
		}
		scanner.close();
		entriesScanner.close();

		return latticeArray;
	}

	// parseFileHeader 
	// Pre-conditions:
	// - latticeEntries is the name of the lattice array
	// Post-conditions:
	// - The lattice array is searched for headers whose values are placed in the corresponding variables
	private void parseFileHeader(String[][] latticeEntries) {
		for (int i = 0; i < latticeEntries.length; i++) {

			if (latticeEntries[i][0].equals("id")) {
				utteranceID = latticeEntries[i][1];
			}
			if (latticeEntries[i][0].equals("start")) {
				startIdx = Integer.parseInt(latticeEntries[i][1]);
			}
			if (latticeEntries[i][0].equals("end")) {
				endIdx = Integer.parseInt(latticeEntries[i][1]);
			}
			if (latticeEntries[i][0].equals("numNodes")) {
				numNodes = Integer.parseInt(latticeEntries[i][1]);
			}
			if (latticeEntries[i][0].equals("numEdges")) {
				numEdges = Integer.parseInt(latticeEntries[i][1]);
			}
		}
	}

	// parseEdges
	// Pre-conditions:
	// - latticeEntries is the name of the lattice array
	// Post-conditions:
	// - The lattice array is searched for edges whose source and destination nodes are 
	//   sent to Edge along with their corresponding weights
	private Edge[][] parseEdges(String[][] latticeEntries) {
		Edge adjMatrix[][] = new Edge[numNodes][numNodes];

		for (int i = 0; i < latticeEntries.length; i++) {
			if (latticeEntries[i][0].equals("edge")) {
				int sourceNode = Integer.parseInt(latticeEntries[i][1]);
				int destNode = Integer.parseInt(latticeEntries[i][2]);
				String utteranceID = latticeEntries[i][3];
				int am = Integer.parseInt(latticeEntries[i][4]);
				int lm = Integer.parseInt(latticeEntries[i][5]);

				adjMatrix[sourceNode][destNode] = new Edge(utteranceID, am, lm);
			}
		}

		return adjMatrix;
	}

	// parseNodeTimes 
	// Pre-conditions:
	// - latticeEntries is the name of the lattice array
	// Post-conditions:
	// - The lattice array is searched for nodes and adds their nodeTime to their corresponding index 
	private double[] parseNodeTimes(String[][] latticeEntries) {

		double[] nodeTimes = new double[numNodes];

		for (int i = 0; i < latticeEntries.length; i++) {
			if (latticeEntries[i][0].equals("node")) {
				int nodeIndex = Integer.parseInt(latticeEntries[i][1]);
				double nodeTime = Double.parseDouble(latticeEntries[i][2]);

				nodeTimes[nodeIndex] = nodeTime;
			}
		}

		return nodeTimes;
	}

	// findInDegrees 
	// Pre-conditions:
	// - adjMatrix is the name of the adjacency matrix for the lattice
	// Post-conditions:
	// - The lattice adjacency matrix is searched and counts the number of non-null row-column pairs,
	//	 placing the number in the row node's inDegrees index.
	private int[] findInDegrees(Edge[][] adjMatrix) {
		int[] inDegrees = new int[adjMatrix.length];
		for (int i = 0; i < adjMatrix.length; i++) {
			for (int j = 0; j < adjMatrix.length; j++) {
				if (adjMatrix[j][i] != null) {
					inDegrees[i]++;
				}
			}
		}
		return inDegrees;
	}

	// createAdjSet 
	// Pre-conditions:
	// - None
	// Post-conditions:
	// - The lattice adjacency matrix is searched for non-null row-column pairs. When a non-null is found,
	//   the column value is placed into the row value's adjacency list.
	private ArrayList<LinkedList<Integer>> createAdjSet() {
		ArrayList<LinkedList<Integer>> adjSet = new ArrayList<LinkedList<Integer>>();

		for (int i = 0; i < numNodes - 1; i++) {
			adjSet.add(new LinkedList<Integer>());
			for (int j = 0; j < numNodes; j++) {
				if (adjMatrix[i][j] != null) {
					adjSet.get(i).add(j);
				}
			}
		}
		return adjSet;
	}
}
