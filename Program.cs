using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;
using System.Threading;


namespace Planning
{
    class Program
    {
        static StreamWriter swResults; // The stream for outputting results
        public static string outputPath = Directory.GetCurrentDirectory() + @"\";
        public static string resultFilePath = "plan.txt";

        public static string defaultProblem = @"logistics00-factored\probLOGISTICS-4-0";

        
        
        public enum PlanerType { ff_tryCoordinate, hsp_tryCoordinate, ff_directPlan, hsp_directPlan, ff_toActions };
        public static PlanerType internalPlaner;

        public enum HighLevelPlanerType { PDB, Landmark, Projection, ForwardHsp, BackwardHsp, LandmarkAndHsp, WeightedLandmarkAndHsp, SophisticatedProjection, MafsLandmark, Mafsff, MafsWithProjectionLandmarks, PDBMafs, ProjectionMafs, DistrebutedProjectionMafs };
        public static HighLevelPlanerType highLevelPlanerType = HighLevelPlanerType.ProjectionMafs;
        
        public enum ProjectionVersion { Local, Global, GlobalV2, GlobalWithMemo, fullGlobal, ProjectionFF, NULL };
        public static ProjectionVersion projectionVersion = ProjectionVersion.ProjectionFF; // Relevant: "Global" is the full plan h + "ProjectionFF" 

        public static List<double> times = new List<double>();
        public static List<double> countActions = new List<double>();
        public static double timeSum = 0;
        public static double actionSum = 0;
        public static double messages = 0;
        public static int StateExpandedCounter = 0;

        public static DateTime Start, StartHighLevelPlanning, StartGrounding, End;
        public static int PlanCost, PlanMakeSpan;

        public static bool VerifyPlan(Domain dJoint, Problem pJoint, List<string> lPlan)
        {
            List<State> lStates = new List<State>();
            State sInitial = new State(pJoint);
            foreach (Predicate p in pJoint.Known)
                sInitial.AddPredicate(p);
            State sCurrent = sInitial;
            int i = 0;
            foreach (string sAction in lPlan)
            {
                State sNew = sCurrent.Apply(sAction);
                if (sNew == null)
                    return false;
                lStates.Add(sNew);
                sCurrent = sNew;
                i++;
            }
            CompoundFormula joinGoal = new CompoundFormula("and");
            foreach (GroundedPredicate gGp in pJoint.Goal.GetAllPredicates())
            {
                if (!gGp.Name.Equals("and"))
                    joinGoal.AddOperand(gGp);
            }
            pJoint.Goal = joinGoal;
            if (pJoint.IsGoalState(sCurrent))
            {
                PlanCost = lPlan.Count;
                return true;
            }
            return false;
        }

        

        public static int MaxMakespanCalculation(List<Agent> agents, List<string> lActionsName, Domain dJoint)
        {
            List<KeyValuePair<string, Action>> sPlan = Runner.GetActions(lActionsName, dJoint, agents);
            State fullInitialState = new State(agents[0].startState);
            Dictionary<string, int> agentsTimeSteps = new Dictionary<string, int>();
            agentsTimeSteps.Add(agents[0].name, 0);
            for (int i = 1; i < agents.Count; i++)
            {
                foreach (var fact in agents[i].startState.m_lPredicates)
                    fullInitialState.AddPredicate(fact);
                agentsTimeSteps.Add(agents[i].name, 0);
            }
            Dictionary<GroundedPredicate, int> gpCost = new Dictionary<GroundedPredicate, int>();
            foreach (GroundedPredicate gp in fullInitialState.m_lPredicates)
            {
                gpCost.Add(gp, 0);
            }


            int timeSteps = 0;
            bool stop = false;
            foreach (var action in sPlan)
            {
                int cost = MaxCost(gpCost, action.Value.Preconditions.GetAllPredicates().ToList());
                if (cost < agentsTimeSteps[action.Key])
                    cost = agentsTimeSteps[action.Key];

                HashSet<Predicate> lDeleteList = new HashSet<Predicate>(), lAddList = new HashSet<Predicate>();
                fullInitialState.GetApplicableEffects(action.Value.Effects, lAddList, lDeleteList);
                foreach (GroundedPredicate dellp in lDeleteList)
                {
                    gpCost.Remove((GroundedPredicate)dellp.Negate());
                }
                foreach (GroundedPredicate addp in lAddList)
                {
                    if (!gpCost.ContainsKey(addp))
                    {
                        gpCost.Add(addp, cost + 1);
                    }
                }
                foreach (GroundedPredicate addp in lDeleteList)
                {
                    if (!gpCost.ContainsKey(addp))
                    {
                        gpCost.Add(addp, cost + 1);
                    }
                }

                agentsTimeSteps[action.Key] = cost + 1;
                fullInitialState = fullInitialState.Apply(action.Value);

            }
            int maxSpan = 0;
            foreach (Agent agent in agents)
            {
                if (agentsTimeSteps[agent.name] > maxSpan)
                    maxSpan = agentsTimeSteps[agent.name];
            }
            return maxSpan;
        }

        public static int MaxCost(Dictionary<GroundedPredicate, int> cost, List<Predicate> pre)
        {
            int MaxCost = 0;
            foreach (GroundedPredicate preGp in pre)
            {
                if (cost[preGp] > MaxCost)
                {
                    MaxCost = cost[preGp];
                }
            }
            return MaxCost;
        }

        public static void WritePlanToFile(List<string> lPlan, string filePath)
        {
            StreamWriter swOutput = new StreamWriter(filePath);

            if (lPlan != null)
            {
                for (int i = 0; i < lPlan.Count; i++)
                {
                    string sOutputName = Domain.MapGroundedActionNamesToOutputNames[lPlan[i]];
                    swOutput.WriteLine(i + " : " + sOutputName);
                    Console.WriteLine(i + " : " + sOutputName);
                }
            }
            swOutput.Close();
        }
        
        /**
         * Output results to the output stream
         **/
        public static void WriteResults(string sDomain, string sMsg)
        {
            Console.WriteLine(sDomain + " " + sMsg);
            swResults = new StreamWriter(outputPath+@"/Results.txt", true);
            swResults.WriteLine(sDomain + ", " + sMsg.Replace(",", ":") + ", " + PlanCost + ", " + PlanMakeSpan
                + "," + (End.Subtract(Start).TotalSeconds - Runner.pdbCreationTime)
            );
            swResults.Close();
            Console.WriteLine("Time: " + (End.Subtract(Start).TotalSeconds - Runner.pdbCreationTime));
            Console.WriteLine("Plan makespan: " + PlanMakeSpan);
        }


        /**
         * The starting point of the program.
         **/
        static void Main(string[] args)
        {            
            Console.WriteLine("Running configuration " + highLevelPlanerType);

            // CASE 0: Run on default problem and default output path
            if (args.Length == 0)
            {
                swResults = new StreamWriter(@"Results.txt", false);
                swResults.Close();
                string sPath =
                    Directory.GetCurrentDirectory() + @"\..\..\benchmarks\"+ defaultProblem;

                // RunUsingProcesses(new DirectoryInfo(sPath), "Plan.txt");
                Runner.ParseAll(new DirectoryInfo(sPath), "Plan.txt");
            }
            // CASE 1: Run on a given problem and default output path
            else if (args.Length == 1)
            {
                Runner.ParseAll(new DirectoryInfo(args[0]), outputPath);
            }
            // CASE 2: Run on a given problem and output results into a given path
            else if (args.Length == 2)
            {
                if (args[1][args[1].Length - 1] == '\'')
                    args[1]=args[1].Remove(args[1].Length - 1);
                outputPath = args[1];
                Runner.ParseAll(new DirectoryInfo(args[0]), args[1]);
            }
            // CASE 3: Run on a specific given set of problems
            else
            {
                List<string> lDomainFiles = new List<string>();
                List<string> lProblemFiles = new List<string>();
                for (int i = 0; i < args.Length - 1; i += 2)
                {
                    lDomainFiles.Add(args[i]);
                    lProblemFiles.Add(args[1]);
                }
                try
                {
                    List<Domain> lDomains = new List<Domain>();
                    List<Problem> lProblems = new List<Problem>();
                    Runner.ReadAgentFiles(lDomainFiles, lProblemFiles, lDomains, lProblems);
                    List<Agent> agents = null;
                    List<string> lPlan = Runner.SolveFactored(lDomains, lProblems, ref agents, null);
                    if (lPlan != null)
                    {
                        WritePlanToFile(lPlan, args[args.Length - 1]+"/Plan.txt");

                        Console.WriteLine();

                    }
                    WriteResults("?", " success");
                }
                catch (Exception e)
                {
                    WriteResults("?", " fail " + e.Message + ", " + e.StackTrace);
                }
            }
        }
    }
}

// Old comments
// ==============
//CreateMABlocksWorld(@"D:\Privacy Preserving\GPPP\GPPP - new format\DOMAINS\factored\newdomainsMABlocksWorld3",
//  6, 7, 5, 6, 7, 8, 1);
// CreateMALogistics(@"D:\Privacy Preserving\GPPP\GPPP - new format\DOMAINS\factored\MALogistics3",
// 10, 12, 10, 13, 10, 12, 1);

/* if (args.Length == 2)
 {
     resultFilePath = args[1];
 }*/
