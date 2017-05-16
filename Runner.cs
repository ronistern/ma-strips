using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;

namespace Planning
{
    class Runner
    {
        public static void ParseAll(DirectoryInfo di, string sOutputPlanFile)
        {
            Program.Start = new DateTime(0);
            Program.StartHighLevelPlanning = new DateTime(0);
            Program.StartGrounding = new DateTime(0);
            Program.End = new DateTime(0);
            Program.PlanCost = -1;
            Program.PlanMakeSpan = -1;

            Console.WriteLine("Scanning directory " + di.Name);
            bool bContainsRealDirectories = false;
            int cSubs = 0;
            if (di.GetDirectories().Length != 0)
            {
                foreach (DirectoryInfo diSub in di.GetDirectories().OrderBy(d => d.Name.ToString()))
                {
                    if (!diSub.Name.ToLower().Contains("pdb"))
                    {
                        ParseAll(diSub, sOutputPlanFile);
                        bContainsRealDirectories = true;
                        cSubs++;

                        //if (cSubs == 2 && di.Name != "factored")
                        //   return;
                    }
                }
            }
            if (!bContainsRealDirectories)
            {
                if (di.ToString().Contains("PdbFiles"))
                    return;
        
                if (sOutputPlanFile == "")
                    sOutputPlanFile = "Plan.txt";
                sOutputPlanFile += "Plan.txt";
                Vertex.agents = new List<Agent>();
                Vertex.ffLplan = new List<string>();
                Vertex.map = new Dictionary<string, int>();
                Vertex.forwardSearch = null;
                Vertex.hsp = null;

                GC.Collect();


                //ReadAgentFiles(di, sOutputPlanFile);

                Thread t = new Thread(() => ReadAgentFiles(di, sOutputPlanFile));

                t.Name = "ReadAgentFiles " + di.Name;
                t.Start();
                if (t.Join(5 * 60 * 1000))
                {
                }
                else
                {
                    t.Abort();
                    // Program.timeResults.WriteLine("*");
                    //Program.timeResults.Flush();
                    Thread.Sleep(1000);
                    //writing an empty plan file
                    StreamWriter sw = new StreamWriter(sOutputPlanFile+"plan.txt");
                    sw.Close();
                    Program.WriteResults(di.Name, " failed - timeout");
                }

                RunUtils.KillPlanners();
            }
        }

        public static void ReadAgentFiles(List<string> lDomainFiles, List<string> lProblemFiles, List<Domain> lDomains, List<Problem> lProblems)
        {
            Console.WriteLine("Parsing");
            for (int i = 0; i < lDomainFiles.Count; i++)
            {
                Parser parser = new Parser();
                Domain d = parser.ParseDomain(lDomainFiles[i]);
                Problem p = parser.ParseProblem(lProblemFiles[i], d);

                lDomains.Add(d);
                lProblems.Add(p);
            }
            foreach (Domain d in lDomains)
            {
                foreach (Action a in d.PublicActions)
                {
                    foreach (Predicate p in a.Effects.GetAllPredicates())
                    {
                        foreach (Domain dOther in lDomains)
                        {
                            if (dOther.AlwaysConstant(p))
                                dOther.m_lAlwaysConstant.Remove(p.Name);

                        }
                    }

                }

            }
        }

        public static void ReadAgentFiles(DirectoryInfo dir, string sOutputFile)
        {
            Console.WriteLine("Reading files " + dir.Name);
            List<string> lDomainFiles = new List<string>();
            List<string> lProblemFiles = new List<string>();
            foreach (FileInfo fi in dir.GetFiles())
            {
                if (fi.Name.Contains("domain"))
                    lDomainFiles.Add(fi.FullName);
                if (fi.Name.Contains("problem"))
                    lProblemFiles.Add(fi.FullName);
            }
            //try
            {
                Domain.ResetStaticVar();
                List<Domain> lDomains = new List<Domain>();
                List<Problem> lProblems = new List<Problem>();
                Domain dJoint = null;
                Problem pJoint = null;
                Runner.ReadAgentFiles(lDomainFiles, lProblemFiles, lDomains, lProblems);
                GetJointDomain(lDomains, lProblems, out dJoint, out pJoint);
                pdbPath = @"PdbFiles/" + dir.Parent.Name;
                if (!Directory.Exists(pdbPath))
                {
                    Directory.CreateDirectory(pdbPath);
                }
                pdbPath += "/" + dir.Name + ".pdb";
                List<Agent> agents = null;
                List<string> lPlan = SolveFactored(lDomains, lProblems, ref agents, dJoint);
                //Program.projResults.WriteLine(
                if (lPlan != null)
                {
                    if (Program.VerifyPlan(dJoint, pJoint, lPlan))
                    {
                        Program.PlanMakeSpan = Program.MaxMakespanCalculation(agents, lPlan, dJoint);
                        Program.WritePlanToFile(lPlan, sOutputFile);
                        Program.WriteResults(dir.Name, " success");
                    }
                    else
                    {   
                        Program.WriteResults(dir.Name, " plan verification failed - could not solve the problem :(");
                    }
                    Console.WriteLine();

                }
                else
                {
                    Program.WritePlanToFile(new List<string>(), sOutputFile);
                    Program.WriteResults(dir.Name, " fail, plan is null");
                }
            }
            //catch (Exception e)
            {
                //WriteResults(dir.Name , " fail, " + e.Message + ", " + e.StackTrace);
            }
        }

        public static List<string> SolveFactored(List<Domain> lDomains, List<Problem> lProblems, ref List<Agent> m_agents, Domain joinDomain)
        {
            if( Program.highLevelPlanerType != Program.HighLevelPlanerType.ProjectionMafs)
            {
                Program.projectionVersion = Program.ProjectionVersion.NULL;
            }
            Program.Start = DateTime.Now;
            pdbCreationTime = 0;
            var lGroundedProblems = GroundProblems(lDomains, lProblems);
            
            Program.internalPlaner = Program.PlanerType.ff_toActions;
            BuildAgents_II buildAgents = new BuildAgents_II(lDomains, lGroundedProblems, lProblems);
            List<Agent> agents = buildAgents.ReturnAgents();

            GetPublicPredicates(agents);
            List<string> lPlan = null;

            if (Program.highLevelPlanerType == Program.HighLevelPlanerType.Projection)
            {
                Console.WriteLine("Planning");
                ShareGoals(agents);
                AdvancedLandmarkProjectionPlaner planner = new AdvancedLandmarkProjectionPlaner();
                lPlan = planner.Plan(agents, lDomains, lProblems, joinDomain);
            }
            else
            {
                try
                {

                    Program.StartHighLevelPlanning = DateTime.Now;
                    if (Program.highLevelPlanerType == Program.HighLevelPlanerType.Landmark)
                    {
                        Console.WriteLine("Identifying landmarks");
                        bool stop = false;
                        while (!stop)
                        {
                            stop = true;
                            string name = "";
                            GroundedPredicate currentGoal = null;
                            foreach (Agent agent in agents)
                            {
                                currentGoal = agent.GetGoal();
                                if (currentGoal != null)
                                {
                                    stop = false;
                                    name = agent.name;
                                    break;
                                }
                            }
                            if (!stop)
                            {
                                foreach (Agent agent in agents)
                                {
                                    if (!agent.name.Equals(name))
                                    {
                                        agent.ReceiveGoal(currentGoal);
                                    }
                                }
                            }

                        }
                        foreach (Agent agent in agents)
                        {
                            agent.InitMutex();
                        }

                        agents = Distributed_Landmarks_Detection.Landmarks_Detection(agents, false);
                        Planer_I Planner = new Planer_I(agents);
                        Console.WriteLine("Planning");
                        lPlan = Planner.Plan();
                    }
                    else
                    {
                        if (Program.highLevelPlanerType == Program.HighLevelPlanerType.PDB)
                        {
                            DateTime startPdbCreation = DateTime.Now;
                            PdbPlaner.pdb = new PatternDatabase(lDomains, lProblems, agents, pdbPath);
                            pdbCreationTime = DateTime.Now.Subtract(startPdbCreation).TotalSeconds;
                            foreach (Agent agent in agents)
                            {
                                agent.InitMutex();
                            }
                            Distributed_Landmarks_Detection.Reset(agents);
                            List<Landmark> PublicAndArtificialGoals = FindPublicAndArtificialGoals(agents);

                            PdbPlaner Planner = new PdbPlaner(agents, PublicAndArtificialGoals, PdbPlaner.pdb);
                            Console.WriteLine("Planning");

                            lPlan = Planner.Plan();

                        }
                        else
                        {
                            if (Program.highLevelPlanerType == Program.HighLevelPlanerType.ForwardHsp)
                            {
                                bool stop = false;
                                while (!stop)
                                {
                                    stop = true;
                                    string name = "";
                                    GroundedPredicate currentGoal = null;
                                    foreach (Agent agent in agents)
                                    {
                                        currentGoal = agent.GetGoal();
                                        if (currentGoal != null)
                                        {
                                            stop = false;
                                            name = agent.name;
                                            break;
                                        }
                                    }
                                    if (!stop)
                                    {
                                        foreach (Agent agent in agents)
                                        {
                                            if (!agent.name.Equals(name))
                                            {
                                                agent.ReceiveGoal(currentGoal);
                                            }
                                        }
                                    }

                                }
                                foreach (Agent agent in agents)
                                {
                                    agent.InitMutex();
                                }
                                Distributed_Landmarks_Detection.Reset(agents);
                                PlanerHsp Planner = new PlanerHsp(agents);
                                Console.WriteLine("Planning");
                                lPlan = Planner.Plan();
                            }
                            else
                            {
                                if (Program.highLevelPlanerType == Program.HighLevelPlanerType.BackwardHsp)
                                {
                                    bool stop = false;
                                    List<GroundedPredicate> publishPublic = new List<GroundedPredicate>();
                                    List<GroundedPredicate> nextPublishPublic = new List<GroundedPredicate>();
                                    foreach (Agent a in agents)
                                    {
                                        publishPublic.AddRange(a.InitBackwardHspGraph());
                                    }
                                    bool outFlag = false;
                                    while (!stop)
                                    {
                                        stop = true;
                                        outFlag = false;
                                        foreach (Agent agent in agents)
                                        {
                                            nextPublishPublic.AddRange(agent.UpdateBackwardHspGraph(publishPublic, out outFlag));
                                            if (outFlag)
                                            {
                                                stop = false;
                                            }
                                        }
                                        publishPublic = nextPublishPublic;
                                    }

                                    foreach (Agent agent in agents)
                                    {
                                        agent.InitMutex();
                                    }
                                    Distributed_Landmarks_Detection.Reset(agents);
                                    // agents = Distributed_Landmarks_Detection.Landmarks_Detection(agents);
                                    PlanerHspII Planner = new PlanerHspII(agents);
                                    Console.WriteLine("Planning");
                                    lPlan = Planner.Plan();

                                }
                                else
                                {
                                    if (Program.highLevelPlanerType == Program.HighLevelPlanerType.LandmarkAndHsp)
                                    {
                                        bool stop = false;
                                        while (!stop)
                                        {
                                            stop = true;
                                            string name = "";
                                            GroundedPredicate currentGoal = null;
                                            foreach (Agent agent in agents)
                                            {
                                                currentGoal = agent.GetGoal();
                                                if (currentGoal != null)
                                                {
                                                    stop = false;
                                                    name = agent.name;
                                                    break;
                                                }
                                            }
                                            if (!stop)
                                            {
                                                foreach (Agent agent in agents)
                                                {
                                                    if (!agent.name.Equals(name))
                                                    {
                                                        agent.ReceiveGoal(currentGoal);
                                                    }
                                                }
                                            }

                                        }
                                        foreach (Agent agent in agents)
                                        {
                                            agent.InitMutex();
                                        }

                                        agents = Distributed_Landmarks_Detection.Landmarks_Detection(agents, false);

                                        PlanerHspAndLandmarks Planner = new PlanerHspAndLandmarks(agents);

                                        Console.WriteLine("Planning..");

                                        lPlan = Planner.Plan();
                                    }
                                    else
                                    {
                                        if (Program.highLevelPlanerType == Program.HighLevelPlanerType.WeightedLandmarkAndHsp)
                                        {
                                            bool stop = false;
                                            while (!stop)
                                            {
                                                stop = true;
                                                string name = "";
                                                GroundedPredicate currentGoal = null;
                                                foreach (Agent agent in agents)
                                                {
                                                    currentGoal = agent.GetGoal();
                                                    if (currentGoal != null)
                                                    {
                                                        stop = false;
                                                        name = agent.name;
                                                        break;
                                                    }
                                                }
                                                if (!stop)
                                                {
                                                    foreach (Agent agent in agents)
                                                    {
                                                        if (!agent.name.Equals(name))
                                                        {
                                                            agent.ReceiveGoal(currentGoal);
                                                        }
                                                    }
                                                }

                                            }
                                            foreach (Agent agent in agents)
                                            {
                                                agent.InitMutex();
                                            }
                                            agents = Distributed_Landmarks_Detection.Landmarks_Detection(agents, false);
                                            PlanerWeightedLandmarkAndHsp Planner = new PlanerWeightedLandmarkAndHsp(agents);
                                            Console.WriteLine("Planning");
                                            lPlan = Planner.Plan();
                                        }
                                        else
                                        {
                                            if (Program.highLevelPlanerType == Program.HighLevelPlanerType.SophisticatedProjection)
                                            {
                                                bool stop = false;
                                                while (!stop)
                                                {
                                                    stop = true;
                                                    string name = "";
                                                    GroundedPredicate currentGoal = null;
                                                    foreach (Agent agent in agents)
                                                    {
                                                        currentGoal = agent.GetGoal();
                                                        if (currentGoal != null)
                                                        {
                                                            stop = false;
                                                            name = agent.name;
                                                            break;
                                                        }
                                                    }
                                                    if (!stop)
                                                    {
                                                        foreach (Agent agent in agents)
                                                        {
                                                            if (!agent.name.Equals(name))
                                                            {
                                                                agent.ReceiveGoal(currentGoal);
                                                            }
                                                        }
                                                    }

                                                }
                                                foreach (Agent agent in agents)
                                                {
                                                    agent.InitMutex();
                                                }
                                                //  agents = AdvancedLandmarkProjectionAgents.CreateProjAgents(agents, lDomains, lProblems);

                                                agents = Distributed_Landmarks_Detection.Landmarks_Detection(agents, false);
                                                PlanerHspAndLandmarks Planner = new PlanerHspAndLandmarks(agents);
                                                Console.WriteLine("Planning");
                                                lPlan = Planner.Plan();
                                            }
                                            else
                                            {
                                                if (Program.highLevelPlanerType == Program.HighLevelPlanerType.PDBMafs)
                                                {
                                                    MapsVertex.pdb = new PatternDatabase(lDomains, lProblems, agents, pdbPath);
                                                    bool stop = false;
                                                    while (!stop)
                                                    {
                                                        stop = true;
                                                        string name = "";
                                                        GroundedPredicate currentGoal = null;
                                                        foreach (Agent agent in agents)
                                                        {
                                                            currentGoal = agent.GetGoal();
                                                            if (currentGoal != null)
                                                            {
                                                                stop = false;
                                                                name = agent.name;
                                                                break;
                                                            }
                                                        }
                                                        if (!stop)
                                                        {
                                                            foreach (Agent agent in agents)
                                                            {
                                                                if (!agent.name.Equals(name))
                                                                {
                                                                    agent.ReceiveGoal(currentGoal);
                                                                }
                                                            }
                                                        }

                                                    }
                                                    foreach (Agent agent in agents)
                                                    {
                                                        agent.InitMutex();
                                                    }


                                                    Console.WriteLine("Planning");

                                                    MapsPlanner Planner = new MapsPlanner(agents, lDomains, lProblems);

                                                    Program.StartGrounding = DateTime.Now;
                                                    lPlan = Planner.Plan();

                                                }
                                                else
                                                if (Program.highLevelPlanerType == Program.HighLevelPlanerType.MafsLandmark)
                                                {
                                                    bool stop = false;
                                                    while (!stop)
                                                    {
                                                        stop = true;
                                                        string name = "";
                                                        GroundedPredicate currentGoal = null;
                                                        foreach (Agent agent in agents)
                                                        {
                                                            currentGoal = agent.GetGoal();
                                                            if (currentGoal != null)
                                                            {
                                                                stop = false;
                                                                name = agent.name;
                                                                break;
                                                            }
                                                        }
                                                        if (!stop)
                                                        {
                                                            foreach (Agent agent in agents)
                                                            {
                                                                if (!agent.name.Equals(name))
                                                                {
                                                                    agent.ReceiveGoal(currentGoal);
                                                                }
                                                            }
                                                        }

                                                    }
                                                    foreach (Agent agent in agents)
                                                    {
                                                        agent.InitMutex();
                                                    }

                                                    agents = Distributed_Landmarks_Detection.Landmarks_Detection(agents, true);

                                                    Console.WriteLine("Planning");

                                                    MapsPlanner Planner = new MapsPlanner(agents, lDomains, lProblems);

                                                    Program.StartGrounding = DateTime.Now;
                                                    lPlan = Planner.Plan();

                                                }
                                                else
                                                if (Program.highLevelPlanerType == Program.HighLevelPlanerType.Mafsff)
                                                {
                                                    bool stop = false;
                                                    while (!stop)
                                                    {
                                                        stop = true;
                                                        string name = "";
                                                        GroundedPredicate currentGoal = null;
                                                        foreach (Agent agent in agents)
                                                        {
                                                            currentGoal = agent.GetGoal();
                                                            if (currentGoal != null)
                                                            {
                                                                stop = false;
                                                                name = agent.name;
                                                                break;
                                                            }
                                                        }
                                                        if (!stop)
                                                        {
                                                            foreach (Agent agent in agents)
                                                            {
                                                                if (!agent.name.Equals(name))
                                                                {
                                                                    agent.ReceiveGoal(currentGoal);
                                                                }
                                                            }
                                                        }

                                                    }
                                                    foreach (Agent agent in agents)
                                                    {
                                                        agent.InitMutex();
                                                    }

                                                    agents = Distributed_Landmarks_Detection.Landmarks_Detection(agents, true);

                                                    Console.WriteLine("Planning");

                                                    MapsPlanner Planner = new MapsPlanner(agents, lDomains, lProblems);

                                                    Program.StartGrounding = DateTime.Now;
                                                    lPlan = Planner.PreferableFFPlan();

                                                }
                                                else                                                
                                                {
                                                    if (Program.highLevelPlanerType == Program.HighLevelPlanerType.ProjectionMafs)
                                                    {
                                                        bool stop = false;
                                                        while (!stop)
                                                        {
                                                            stop = true;
                                                            string name = "";
                                                            GroundedPredicate currentGoal = null;
                                                            foreach (Agent agent in agents)
                                                            {
                                                                currentGoal = agent.GetGoal();
                                                                if (currentGoal != null)
                                                                {
                                                                    stop = false;
                                                                    name = agent.name;
                                                                    break;
                                                                }
                                                            }
                                                            if (!stop)
                                                            {
                                                                foreach (Agent agent in agents)
                                                                {
                                                                    if (!agent.name.Equals(name))
                                                                    {
                                                                        agent.ReceiveGoal(currentGoal);
                                                                    }
                                                                }
                                                            }

                                                        }
                                                        foreach (Agent agent in agents)
                                                        {
                                                            agent.InitMutex();
                                                        }

                                                        agents = Distributed_Landmarks_Detection.Landmarks_Detection(agents, true);

                                                        Console.WriteLine("Planning");

                                                        MapsPlanner Planner = new MapsPlanner(agents, lDomains, lProblems);

                                                        Program.StartGrounding = DateTime.Now;
                                                        
                                                        lPlan = Planner.PreferablePlan();

                                                    }
                                                    else
                                                    if (Program.highLevelPlanerType == Program.HighLevelPlanerType.DistrebutedProjectionMafs)
                                                    {
                                                        bool stop = false;
                                                        while (!stop)
                                                        {
                                                            stop = true;
                                                            string name = "";
                                                            GroundedPredicate currentGoal = null;
                                                            foreach (Agent agent in agents)
                                                            {
                                                                currentGoal = agent.GetGoal();
                                                                if (currentGoal != null)
                                                                {
                                                                    stop = false;
                                                                    name = agent.name;
                                                                    break;
                                                                }
                                                            }
                                                            if (!stop)
                                                            {
                                                                foreach (Agent agent in agents)
                                                                {
                                                                    if (!agent.name.Equals(name))
                                                                    {
                                                                        agent.ReceiveGoal(currentGoal);
                                                                    }
                                                                }
                                                            }

                                                        }
                                                        foreach (Agent agent in agents)
                                                        {
                                                            agent.InitMutex();
                                                        }

                                                        agents = Distributed_Landmarks_Detection.Landmarks_Detection(agents, true);

                                                        Console.WriteLine("Planning");

                                                        MapsPlanner Planner = new MapsPlanner(agents, lDomains, lProblems);

                                                        Program.StartGrounding = DateTime.Now;
                                                        lPlan = Planner.DistrebutedPreferablePlan();

                                                    }
                                                    else
                                                    {
                                                        Console.WriteLine("highLevelPlanerType did not selected");
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }

                    }
                }
                catch (Exception ex)
                {
                    RunUtils.KillPlanners();
                    return null;
                }
            }
            Program.End = DateTime.Now;
            RunUtils.KillPlanners();
            m_agents = agents;
            return lPlan;
        }

        /**
         * TODO: Not clear what this does. It looks like there's a bug here.
         **/
        private static void ShareGoals(List<Agent> agents)
        {
            bool stop = false;
            while (!stop)
            {
                stop = true;
                string name = "";
                GroundedPredicate currentGoal = null;
                foreach (Agent agent in agents)
                {
                    currentGoal = agent.GetGoal();
                    if (currentGoal != null)
                    {
                        stop = false;
                        name = agent.name;
                        break;
                    }
                }
                if (!stop)
                {
                    foreach (Agent agent in agents)
                    {
                        if (!agent.name.Equals(name))
                        {
                            agent.ReceiveGoal(currentGoal);
                        }
                    }
                }
            }
        }

        /**
         * Extract the list of public predicates known to all agents
         **/
        private static Dictionary<string, HashSet<GroundedPredicate>> GetPublicPredicates(List<Agent> agents)
        {
            Dictionary<string, HashSet<GroundedPredicate>> allPublicPredicate =
                new Dictionary<string, HashSet<GroundedPredicate>>();
            foreach (Agent agent in agents)
            {
                allPublicPredicate.Add(agent.name, new HashSet<GroundedPredicate>());
                foreach (Action publicAct in agent.publicActions)
                {
                    foreach (GroundedPredicate pre in publicAct.HashPrecondition)
                    {
                        if (agent.PublicPredicates.Contains(pre))
                        {
                            allPublicPredicate[agent.name].Add(pre);
                        }
                    }

                    foreach (GroundedPredicate eff in publicAct.HashEffects)
                    {
                        if (agent.PublicPredicates.Contains(eff))
                        {
                            allPublicPredicate[agent.name].Add(eff);
                        }
                    }
                }
                /* foreach (GroundedPredicate gp in agent.PublicPredicates)
                 {
                     allPublicPredicate[agent.name].Add(gp);
                 }*/
            }
            foreach (Agent agent in agents)
            {
                // agent.ReducePublicActions(allPublicPredicate);
            }

            return allPublicPredicate;
        }

        /**
         * Ground the problems (i.e., convert from factored planning to unfactored)
         **/
        private static List<Domain> GroundProblems(List<Domain> lDomains, List<Problem> lProblems)
        {
            Console.WriteLine("Grounding");
            BuildAgents_II.mapActionNameToAgents = new Dictionary<string, HashSet<string>>();
            bool bNewPublicFacts = true;
            HashSet<GroundedPredicate> lPublicFacts = new HashSet<GroundedPredicate>();
            for (int i = 0; i < lDomains.Count; i++)
            {
                lDomains[i].StartGrounding(lProblems[i], lPublicFacts);
            }

            while (bNewPublicFacts)
            {
                int cPublicFacts = lPublicFacts.Count;
                for (int i = 0; i < lDomains.Count; i++)
                {
                    lDomains[i].ContinueGrounding(lProblems[i], lPublicFacts);
                }
                bNewPublicFacts = lPublicFacts.Count > cPublicFacts;
            }
            List<Domain> lGrounded = new List<Domain>();
            for (int i = 0; i < lDomains.Count; i++)
            {
                lGrounded.Add(lDomains[i].FinishGrounding(i));
            }
            return lGrounded;
            
            /* if (UseHacks)
             {
                 Console.WriteLine("Attempting hacks");
                 lPlan = SolveSingleAgent(lGrounded, lProblems);
                 if (lPlan != null)
                 {
                     WritePlanToFile(lPlan, sOutputDirectory + "/" + sOutputFile);
                     return;
                 }
                 lPlan = SolveUsingProjectedPublicActions(lGrounded, lProblems);
             }*/
        }

        public static double pdbCreationTime;

        public static List<Landmark> FindPublicAndArtificialGoals(List<Agent> agents)
        {
            List<Landmark> PublicAndArtificialGoals = new List<Landmark>();
            foreach (Agent agent in agents)
            {
                List<Landmark> agentsGoal = agent.GetPublicAndArtificialGoal();

                for (int i = 0; i < agentsGoal.Count; i++)
                {
                    Landmark newGoal = agentsGoal.ElementAt(i);
                    if (!PublicAndArtificialGoals.Contains(newGoal, new LandmarkEqualityComparer()))
                    {
                        PublicAndArtificialGoals.Add(newGoal);
                    }
                }
            }
            return PublicAndArtificialGoals;
        }

        public static string pdbPath;

        public static void GetJointDomain(List<Domain> lDomains, List<Problem> lProblems, out Domain dJoint, out Problem pJoint)
        {
            dJoint = lDomains[0].Clone();
            pJoint = lProblems[0].Clone();
            pJoint.Domain = dJoint;
            CompoundFormula cfAnd = new CompoundFormula("and");
            cfAnd.AddOperand(pJoint.Goal);
            for (int i = 1; i < lDomains.Count; i++)
            {
                dJoint.Actions.AddRange(lDomains[i].Actions);
                dJoint.Predicates.UnionWith(lDomains[i].Predicates);
                dJoint.Constants.UnionWith(lDomains[i].Constants);
                foreach (Predicate pKnown in lProblems[i].Known)
                    pJoint.AddKnown(pKnown);
                cfAnd.AddOperand(lProblems[i].Goal);
            }
            pJoint.Goal = cfAnd.Simplify();
        }

        public static List<KeyValuePair<string, Action>> GetActions(List<string> lActionsName, Domain dJoint, List<Agent> agents)
        {
            List<KeyValuePair<string, Action>> sPlan = new List<KeyValuePair<string, Action>>();
            foreach (string actName in lActionsName)
            {
                string sOutputName = Domain.MapGroundedActionNamesToOutputNames[actName];
                sOutputName = sOutputName.Substring(1, sOutputName.Length - 2);
                Action act = dJoint.GroundActionByName(sOutputName.Split(' '));
                bool fails = true;
                foreach (Agent agent in agents)
                {
                    if (agent.m_actions.Contains(act))
                    {
                        sPlan.Add(new KeyValuePair<string, Action>(agent.name, act));
                        fails = false;
                        break;
                    }
                }
                if (fails)
                    throw new Exception();
            }
            return sPlan;
        }
    }
}
