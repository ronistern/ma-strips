using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Planning
{
    class MapsPlanner
    {
        public static int generateCounter = 0;
        public static bool stop = false;
        public static int massageEffCounter = 0;
        public static int massagePreCounter = 0;
        public static HashSet<GroundedPredicate> allPublicFacts = null;
        List<MapsAgent> MapsAgents = null;
        Dictionary<string, HashSet<MapsVertex>> openLists = null;
        Dictionary<string, HashSet<MapsVertex>> receivedStates = null;
        Dictionary<string, Mutex> mutexs = null;
        Dictionary<string, int> countOfLandmarks = null;
        Dictionary<string, int> countOfReasenOrders = null;
        //public static DateTime begin ;
        public static HashSet<string> sendedToAllSign = null;
        Dictionary<Agent, HashSet<GroundedPredicate>> agentsPublicPreconditions = null;
        Dictionary<Agent, HashSet<GroundedPredicate>> agentsPublicEffects = null;
        public static Dictionary<string, HashSet<string>> actionMap = null;
        public static Dictionary<string, Dictionary<string, HashSet<Action>>> AgentToInfluActions = null;
        public static Dictionary<string, List<string>> influencedByAgents = null;
        public static Dictionary<string, Dictionary<string, HashSet<string>>> recoverActionEffect = null;

        public MapsPlanner(List<Agent> agents,List<Domain> lDomains, List<Problem> lProblems)
        {
            agentsPublicPreconditions = new Dictionary<Agent, HashSet<GroundedPredicate>>();
            agentsPublicEffects = new Dictionary<Agent, HashSet<GroundedPredicate>>();
            recoverActionEffect = new Dictionary<string, Dictionary<string, HashSet<string>>>();
            List<GroundedPredicate> allGoals = new List<GroundedPredicate>();
            sendedToAllSign = new HashSet<string>();
            actionMap = new Dictionary<string, HashSet<string>>();
            AgentToInfluActions = new Dictionary<string, Dictionary<string, HashSet<Action>>>();
            influencedByAgents = new Dictionary<string, List<string>>();
            stop = false;
            MacroAction.counter = 1;
            receivedStates = new Dictionary<string, HashSet<MapsVertex>>();
            openLists = new Dictionary<string, HashSet<MapsVertex>>();
            mutexs = new Dictionary<string, Mutex>();
            countOfLandmarks = new Dictionary<string, int>();
            countOfReasenOrders = new Dictionary<string, int>();
            Dictionary<string, int> indexStates = new Dictionary<string, int>();
            allPublicFacts = new HashSet<GroundedPredicate>();
            foreach (Agent a in agents)
            {
                allGoals = allGoals.Union(a.goal).ToList();
                sendedToAllSign.Add(a.name);

            }
            HashSet<GroundedPredicate> allG = new HashSet<GroundedPredicate>(allGoals);
            foreach (Agent a in agents)
            {
                a.initPlaner();
                for (int i = 0; i < a.publicActions.Count; i++)
                {
                    Action act = a.publicActions[i];
                    foreach (GroundedPredicate gp in act.HashEffects)
                    {
                        if ((a.PublicPredicates.Contains(gp) || a.PublicPredicates.Contains((GroundedPredicate)gp.Negate())) && gp.Negation)
                        {
                            act.isDeletePublic = true;
                            break;
                        }
                    }
                    foreach (GroundedPredicate gp in act.HashPrecondition)
                    {
                        if (a.PublicPredicates.Contains(gp))
                        {
                            if (act.HashEffects.Contains((GroundedPredicate)gp.Negate()))
                                continue;
                            ((CompoundFormula)act.Effects).AddOperand(gp);
                            act.HashEffects.Add(gp);
                        }

                    }
                }
                HashSet<GroundedPredicate> preconditions = a.GetAllPublicPreconditions();
                //preconditions.UnionWith(allGoals);
                agentsPublicPreconditions.Add(a, preconditions);
                agentsPublicEffects.Add(a, a.GetAllPublicEffects());
                indexStates.Add(a.name, 0);

                receivedStates.Add(a.name, new HashSet<MapsVertex>());
                openLists.Add(a.name, new HashSet<MapsVertex>());
                mutexs.Add(a.name, new Mutex());
                countOfLandmarks.Add(a.name, a.publicRelevantLandmark.Count);
                countOfReasenOrders.Add(a.name, a.ReasonableOrdering.Count);

                foreach (GroundedPredicate pGp in a.PublicPredicates)
                {
                    allPublicFacts.Add(pGp);
                }
                /* foreach (GroundedPredicate pGp in a.goal)
                 {
                     GroundedPredicate ngp = (GroundedPredicate)pGp.Negate();
                     allPublicFacts.Add(ngp);
                     allPublicFacts.Add(pGp);
                 }*/
            }
            MapsVertex.init(agents);
            List<GroundedPredicate> fullStart = new List<GroundedPredicate>();
            foreach (Agent a in agents)
            {
                foreach (GroundedPredicate gp in a.startState.m_lPredicates)
                {
                    fullStart.Add(gp);
                }
            }
            HashSet<GroundedPredicate> publicStartState = new HashSet<GroundedPredicate>();
            Dictionary<string, State> agPriv = new Dictionary<string, State>();
            foreach (Agent a in agents)
            {
                State privateStartState = new State((Problem)null);

                foreach (GroundedPredicate gp in a.startState.m_lPredicates)
                {
                    if (!a.PublicPredicates.Contains(gp))
                        privateStartState.AddPredicate(gp);
                    else
                    {
                        publicStartState.Add(gp);
                    }
                }
                agPriv.Add(a.name, privateStartState);

            }
            List<MapsVertex> lVertexes = new List<MapsVertex>();
            Dictionary<string, MapsAgent> MapsAgents = new Dictionary<string, MapsAgent>();
            this.MapsAgents = new List<MapsAgent>();
            foreach (Agent a in agents)
            {
                MapsVertex agentStartVertex = new MapsVertex(publicStartState, agPriv[a.name], indexStates, countOfLandmarks, countOfLandmarks.Keys.ToArray(), a.name, a.allGoals.Count, countOfReasenOrders);
                MapsAgent mAgent = new MapsAgent(agentStartVertex, a, a.allGoals, countOfLandmarks, openLists, receivedStates, mutexs, countOfReasenOrders, fullStart);
                mAgent.projectionHeuristic = new AdvancedProjectionHeuristic(a, agents, lDomains, lProblems);
                mAgent.SetPrivateState(agPriv[a.name]);
                MapsAgents.Add(mAgent.name, mAgent);
                this.MapsAgents.Add(mAgent);
                lVertexes.Add(agentStartVertex);
            }
            MapsVertex.UpDateAgents(MapsAgents);
            foreach (MapsVertex v in lVertexes)
            {
                v.PreaperFirstVertex();
            }
            foreach (Agent a in agents.ToList())
            {
                recoverActionEffect.Add(a.name, new Dictionary<string, HashSet<string>>());
                foreach (Action act in a.publicActions)
                {
                    recoverActionEffect[a.name].Add(act.Name, new HashSet<string>());
                    bool breaking = false;
                    foreach (GroundedPredicate eff in act.HashEffects)
                    {
                        if (eff.Negation)
                        {
                            foreach (Agent a2 in agents.ToList())
                            {
                                if (a2.name.Equals(a.name))
                                    continue;
                                HashSet<GroundedPredicate> agentEff = agentsPublicEffects[a2];
                                if (agentEff.Contains((GroundedPredicate)eff.Negate()))
                                {
                                    recoverActionEffect[a.name][act.Name].Add(a2.name);
                                    breaking = true;
                                    break;
                                }
                            }
                            if (breaking)
                                break;
                        }
                    }

                }
                AgentToInfluActions.Add(a.name, new Dictionary<string, HashSet<Action>>());
                foreach (Action act in a.publicActions)
                {
                    if (!actionMap.ContainsKey(act.Name))
                        actionMap.Add(act.Name, new HashSet<string>());
                    foreach (var pair in agentsPublicPreconditions)
                    {
                        //  if (a.Equals(pair.Key))
                        //    continue;
                        bool flag = false;
                        foreach (GroundedPredicate eff in act.HashEffects)
                        {
                            if (pair.Value.Contains(eff))
                            {
                                flag = true;
                                break;
                            }
                        }
                        if (flag)
                        {
                            actionMap[act.Name].Add(pair.Key.name);
                        }
                    }
                }
                influencedByAgents.Add(a.name, new List<string>());
                foreach (Agent a2 in agents.ToList())
                {
                    AgentToInfluActions[a.name].Add(a2.name, new HashSet<Action>());
                    foreach (Action act in a.publicActions)
                    {

                        bool effFlag = false;
                        foreach (GroundedPredicate eff in act.HashEffects)
                        {
                            if (agentsPublicPreconditions[a2].Contains(eff))
                            {
                                effFlag = true;
                                break;
                            }
                        }

                        if (effFlag)
                        {
                            AgentToInfluActions[a.name][a2.name].Add(act);
                        }
                    }


                    if (a.name.Equals(a2.name))
                        continue;
                    bool flag = false;
                    foreach (GroundedPredicate pre in agentsPublicPreconditions[a])
                    {
                        if (agentsPublicEffects[a2].Contains(pre))
                        {
                            influencedByAgents[a.name].Add(a2.name);
                            break;
                        }
                    }
                }
            }
        }
        public List<string> Plan()
        {
            //List<Thread> threads = new List<Thread>();
            //begin = DateTime.Now;
            countMacro = 0.0;
            ffMessageCounter = 0;
            countAvgPerMacro = 0.0;
            sendedStateCounter = 0;
            Program.StateExpandedCounter = 0;
            MapsPlanner.generateCounter = 0;
            notSandedStates = 0;
            List<string> lplan = null;
            while (lplan == null)
            {
                foreach (MapsAgent agent in MapsAgents)
                {
                    lplan = agent.BeginPlanning();
                    if (lplan != null)
                        break;

                }


                if (lplan != null)
                {
                    MapsPlanner.stop = true;
                    break;
                }

            }
            return lplan;

        } 
        public static Dictionary<string, HashSet<MapsVertex>> nextGlobalOpenList = null;

        public static bool directMessage = false;
        public List<string> PreferablePlan()
        {
            if (!directMessage)
                return PreferablePlan_NotdirectMessage();
            else
                return PreferablePlan_DirectMessage();

        }

        public List<string> PreferablePlan_NotdirectMessage()
        {
            //List<Thread> threads = new List<Thread>();
            //begin = DateTime.Now;
            //return null;
            countMacro = 0.0;
            countAvgPerMacro = 0.0;
            sendedStateCounter = 0;
            ffMessageCounter = 0;
            Program.StateExpandedCounter = 0;
            notSandedStates = 0;
            MapsPlanner.generateCounter = 0;
            makeSpanPlanTime = 0.0;
            List<string> lplan = null;
            MapsAgent.InitMutex(MapsAgents);
            
            List<double> iterationTimes = null;
            MapsAgent.thereIsPrivate = false;
            foreach (MapsAgent agent in MapsAgents)
            {
                if(agent.privateActions.Count>0)
                {
                    MapsAgent.thereIsPrivate = true;
                }
            }
            int x = 0;
            while (lplan == null)
            {
                nextGlobalOpenList = new Dictionary<string, HashSet<MapsVertex>>();
                foreach (MapsAgent agent in MapsAgents)
                {
                    nextGlobalOpenList.Add(agent.name, new HashSet<MapsVertex>());
                }
                iterationTimes = new List<double>();
              
                
               
                foreach (MapsAgent agent in MapsAgents)
                {
                    DateTime startTime = DateTime.Now;
                    lplan = agent.BeginPreferablePlanning();
                    iterationTimes.Add(DateTime.Now.Subtract(startTime).TotalSeconds);
                    if (lplan != null)
                        break;
                }
              /*  bool chacking = false;
                foreach (MapsAgent agent in MapsAgents)
                {
                    if (agent.GetCountOfPreferableList() > 0)
                        chacking = true;

                }
                foreach(HashSet<MapsVertex> l in nextGlobalOpenList.Values)
                {
                    foreach(MapsVertex mv in l)
                    {
                        if (mv.isPreferable)
                            chacking = true;
                    }
                }
                Console.WriteLine(x);
                if (!chacking && x != 0)
                    Console.WriteLine("ddd");
                x++;*/
                double maxTime = iterationTimes.Max();
                makeSpanPlanTime += maxTime;

                if (lplan != null)
                {
                    MapsPlanner.stop = true;
                    break;
                }
                else
                {
                    foreach (MapsAgent agent in MapsAgents)
                    {
                        agent.SetPublicOpenLists(nextGlobalOpenList);
                    }
                }
            }
            return lplan;

        }
        public List<string> PreferablePlan_DirectMessage()
        {
            //List<Thread> threads = new List<Thread>();
            //begin = DateTime.Now;
            //return null;
            countMacro = 0.0;
            countAvgPerMacro = 0.0;
            sendedStateCounter = 0;
            ffMessageCounter = 0;
            Program.StateExpandedCounter = 0;
            notSandedStates = 0;
            MapsPlanner.generateCounter = 0;
            makeSpanPlanTime = 0.0;
            List<string> lplan = null;
            MapsAgent.InitMutex(MapsAgents);

            List<double> iterationTimes = null;
            MapsAgent.thereIsPrivate = false;
            foreach (MapsAgent agent in MapsAgents)
            {
                if (agent.privateActions.Count > 0)
                {
                    MapsAgent.thereIsPrivate = true;
                }
            }
            int x = 0;
            while (lplan == null)
            {
                
                iterationTimes = new List<double>();



                foreach (MapsAgent agent in MapsAgents)
                {
                    DateTime startTime = DateTime.Now;
                    lplan = agent.BeginPreferablePlanning();
                    iterationTimes.Add(DateTime.Now.Subtract(startTime).TotalSeconds);
                    if (lplan != null)
                        break;
                }
               
                double maxTime = iterationTimes.Max();
                makeSpanPlanTime += maxTime;

                if (lplan != null)
                {
                    MapsPlanner.stop = true;
                    break;
                }
            }
            return lplan;

        }
        public List<string> PreferableFFPlan()
        {
            //List<Thread> threads = new List<Thread>();
            //begin = DateTime.Now;
            countMacro = 0.0;
            countAvgPerMacro = 0.0;
            sendedStateCounter = 0;
            ffMessageCounter = 0;
            Program.StateExpandedCounter = 0;
            notSandedStates = 0;
            makeSpanPlanTime = 0.0;
            MapsPlanner.generateCounter = 0;
            List<string> lplan = null;
            MapsAgent.InitMutex(MapsAgents);
            List<double> iterationTimes = null;

            while (lplan == null)
            {
                nextGlobalOpenList = new Dictionary<string, HashSet<MapsVertex>>();
                foreach (MapsAgent agent in MapsAgents)
                {
                    nextGlobalOpenList.Add(agent.name, new HashSet<MapsVertex>());
                }
                iterationTimes = new List<double>();
                foreach (MapsAgent agent in MapsAgents)
                {
                    DateTime startTime = DateTime.Now;
                    lplan = agent.BeginPreferableFFPlanning();
                    iterationTimes.Add(DateTime.Now.Subtract(startTime).TotalSeconds);
                    if (lplan != null)
                        break;

                }

                double maxTime = iterationTimes.Max();
                makeSpanPlanTime += maxTime;

                if (lplan != null)
                {
                    MapsPlanner.stop = true;
                    break;
                }
                else
                {
                    foreach (MapsAgent agent in MapsAgents)
                    {
                        agent.SetPublicOpenLists(nextGlobalOpenList);
                    }
                }

            }
            return lplan;

        }
        public static bool findGoal=false;
        public static List<string> finalPlan = null;
        //public static Mutex goalChackMutex = null;
        
       // public static Dictionary<string, Mutex> globalListMutex = null;
        public List<string> DistrebutedPreferablePlan()
        {
            //List<Thread> threads = new List<Thread>();
            //begin = DateTime.Now;
            // goalChackMutex = new Mutex();
            // heursticCalcultionMutex = new Mutex();
            //tmpMutex = new Mutex();

            MapsAgent.InitMutex(MapsAgents);
            countMacro = 0.0;
            ffMessageCounter = 0;
            countAvgPerMacro = 0.0;
            sendedStateCounter = 0;
            Program.StateExpandedCounter = 0;
            notSandedStates = 0;
            MapsPlanner.generateCounter = 0;
            List<string> lplan = null;
            List<Thread> threads = new List<Thread>();
            /*
            for(int i=MapsAgents.Count-1;i>-1;i--)
            {
                MapsAgent agent = MapsAgents.ElementAt(i);
                Thread t = new Thread(agent.BeginDistrebutedPreferablePlanning);
                threads.Add(t);
                t.Start();
            }
            */
           foreach (MapsAgent agent in MapsAgents)
            {
                Thread t = new Thread(agent.BeginDistrebutedPreferablePlanning);
                t.Name = agent.name;
                threads.Add(t);                
                t.Start();              
            }

          foreach(Thread t in threads)
            {
                t.Join();
            }

            
            return finalPlan;

        }

        public static double countAvgPerMacro = 0.0;
        public static double countMacro = 0.0;
        public static int ffMessageCounter = 0;
        static public int notSandedStates = 0;
        static public double makeSpanPlanTime = 0;
        public static int sendedStateCounter = 0;
    }
}
