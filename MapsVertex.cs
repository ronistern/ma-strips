using System;
using System.Collections.Generic;
using System.Linq;

namespace Planning
{
    class MapsVertex
    {
        public static HashSet<Predicate>  agentsGoals =null;
        public string afterMe = null;
        public List<string> relaxPlan = null;
        public HashSet<GroundedPredicate> preferFacts = null;
        public List<Action> projectionPlan = null; 
        public int code = -1;
        public bool isFromClosList = false;
        public Dictionary<string, List<Action>> agentsAproxPlan = null;
        public Dictionary<string, List<Action>> MemAgentsAproxPlan = null;
        public bool changingAgent = false;
        public List<Action> localPlan = null;
        public bool isPreferable = false;
        public bool fromOthers = false;
        public Dictionary<string, int> others_h = null;
        public Dictionary<string, HashSet<Predicate>> othersCourrentState = null;
        public static PatternDatabase pdb = null;
        Dictionary<GroundedPredicate, KeyValuePair<string, int>> goalCost = null;
        // public static List<Order> GlobalReasonableOrderingVector = new List<Order>();
        // public static List<Landmark> publicLandmarks = new List<Landmark>();
        public bool fromCloseList = false;
        //public Dictionary<string, bool[]> satisfiedVector = null;
        public bool isComplex = false;
        public List<string> returnTo = null;
        public HashSet<string> shareWith = null;
        public HashSet<string> notReceiveToAgents = null;
        public bool clearCounter = false;
        public int privateActionCounter = 0;
        public List<Action> lplan = null;
        public int lastPrivateIndex = 0;
        public MapsVertex lastPublic = null;
        private static Dictionary<string, Agent> agents = null;
        private static Dictionary<string, MapsAgent> mapsAgents = null;
        public State state = null;
        public static bool isLandmark = false;
        public MapsVertex publicParent = null;
        public HashSet<GroundedPredicate> publicFacts = null;
        public Dictionary<string, int> stateIndexes = null;
        //public Dictionary <string,bool[]> landmarkVector = null;
        //public Dictionary<string, bool[]> ReasonableOrderingVector = null;
        //public bool[] publicLandmarkVector = null;
        //public bool[] publicReasonableOrderingVector = null;
        public string agent;
        public int g = 0;
        public int h;
        public int h2;
        //public int gh;
        public int publicCount;
        public static HashSet<GroundedPredicate> allGoals = null;
        public static void init(List<Agent> agents)
        {
            //publicLandmarks = new List<Landmark>();
            //GlobalReasonableOrderingVector = new List<Order>();
            if (Program.highLevelPlanerType.ToString().ToLower().Contains("landmark"))
                isLandmark = true;
            MapsVertex.agents = new Dictionary<string, Agent>();
            mapsAgents = null;
            allGoals = new HashSet<GroundedPredicate>();
            foreach (Agent agent in agents)
            {
                foreach (GroundedPredicate goal in agent.goal)
                {
                    allGoals.Add(goal);
                }
                MapsVertex.agents.Add(agent.name, agent);
                /* foreach (Landmark l in agent.publicLandmarks)
                 {
                     if (!publicLandmarks.Contains(l))
                         publicLandmarks.Add(l);
                 }
                 foreach (Order o in agent.ReasonableOrdering)
                 {
                     if (!GlobalReasonableOrderingVector.Contains(o))
                         GlobalReasonableOrderingVector.Add(o);
                 }*/
            }
            agentsGoals = new HashSet<Predicate>();
            foreach (Agent agent in agents)
            {
                foreach (GroundedPredicate gp in agent.goal)
                {
                    agentsGoals.Add(gp);
                }
            }

        }


        public static void UpDateAgents(Dictionary<string, MapsAgent> mapsagents)
        {
            mapsAgents = mapsagents;

        }

        public Dictionary<string, bool[][]> vectors = null;
        public bool[] SatisfactionLandmarks = null;
        public bool[] anyTimeSatisfactionLandmarks = null;

        public MapsVertex(HashSet<GroundedPredicate> m_publicFacts, State privateState, Dictionary<string, int> m_stateIndexes, Dictionary<string, int> countOfAllLandmark, string[] agents, string m_agent, int m_gh, Dictionary<string, int> countOfReasonableOrdering)
        {
            stateIndexes = m_stateIndexes;

            publicCount = 0;
            lplan = new List<Action>();
            publicFacts = new HashSet<GroundedPredicate>(m_publicFacts);
            state = new State((Problem)null);
            foreach (GroundedPredicate gp in privateState.m_lPredicates)
            {
                state.AddPredicate(gp);
            }
            foreach (GroundedPredicate pgp in publicFacts)
            {
                state.AddPredicate(pgp);
            }
            g = 0;
            agent = m_agent;
            lastPrivateIndex = stateIndexes[agent];

            lastPublic = this;
            //gh = m_gh;
        }
        public void PreaperFirstVertex()
        {
            vectors = new Dictionary<string, bool[][]>();
            //satisfiedVector = new Dictionary<string, bool[]>();
            foreach (var a in mapsAgents)
            {

                if (a.Key.Equals(agent))
                {
                    vectors.Add(a.Key, a.Value.GetInitialVectors(state));
                    //satisfiedVector.Add(a.Key, a.Value.GetInitialVectors(state)[0]);
                }
                else
                {
                    State tmpState = new State((Problem)null);
                    foreach (GroundedPredicate gp in a.Value.GetPrivateState(stateIndexes[a.Key]).m_lPredicates)
                    {
                        tmpState.AddPredicate(gp);
                    }
                    foreach (GroundedPredicate pgp in publicFacts)
                    {
                        tmpState.AddPredicate(pgp);
                    }

                    vectors.Add(a.Key, a.Value.GetInitialVectors(tmpState));
                    //satisfiedVector.Add(a.Key, a.Value.GetInitialVectors(tmpState)[0]);
                }


            }
            SatisfactionLandmarks = new bool[vectors.ElementAt(0).Value[0].Length];
            anyTimeSatisfactionLandmarks = new bool[vectors.ElementAt(0).Value[0].Length];
            for (int i = 0; i < anyTimeSatisfactionLandmarks.Length; i++)
            {
                foreach (bool[][] v in vectors.Values)
                {
                    if (v[0][i])
                    {
                        SatisfactionLandmarks[i] = true;
                        anyTimeSatisfactionLandmarks[i] = true;
                        break;
                    }
                }
            }
            h = 0;

            for (int j = 0; j < SatisfactionLandmarks.Length; j++)
            {

                if (!SatisfactionLandmarks[j])
                {
                    h++;
                }
            }
            if (!isLandmark)
            {
                h = 1000;
            }
            if (Program.highLevelPlanerType.ToString().ToLower().Contains("pdb"))
            {
                State partialState = new State((Problem)null);
                foreach (GroundedPredicate pGp in publicFacts)
                {
                    partialState.m_lPredicates.Add(pGp);
                }

                foreach (var ma in mapsAgents)
                {
                    State pState = ma.Value.GetPrivateState(stateIndexes[ma.Key]);
                    foreach (GroundedPredicate gp in pState.m_lPredicates)
                    {
                        partialState.m_lPredicates.Add(gp);
                    }
                }
                h = InitGoalCost(pdb, partialState);
            }
            else
            if (Program.highLevelPlanerType.ToString().ToLower().Contains("projection"))
            {
                /*State partialState = new State((Problem)null);
                foreach (GroundedPredicate pGp in publicFacts)
                {
                    partialState.m_lPredicates.Add(pGp);
                }

                foreach (var ma in mapsAgents)
                {
                    State pState = ma.Value.GetPrivateState(stateIndexes[ma.Key]);
                    foreach (GroundedPredicate gp in pState.m_lPredicates)
                    {
                        partialState.m_lPredicates.Add(gp);
                    }
                }*/
                othersCourrentState = new Dictionary<string, HashSet<Predicate>>();
                h = 1000;
                //  h = GetProjection_h();
            }
            //  h2 = ComputeFF_h();

        }


        public MapsVertex(MapsVertex v)
        {
            publicCount = v.publicCount;
            agent = v.agent;
            lplan = new List<Action>(v.lplan);
            //state = new State(v.state);
            state = new State((Problem)null);
            state.m_lPredicates = new HashSet<Predicate>(v.state.m_lPredicates);

            publicFacts = new HashSet<GroundedPredicate>(v.publicFacts);


            g = v.g;
            h = v.h;

            this.stateIndexes = new Dictionary<string, int>(v.stateIndexes);

            //gh = v.gh;
        }
        public void fullCopy(MapsVertex v)
        {
            if (isLandmark)
            {
                vectors = new Dictionary<string, bool[][]>();
                foreach (var vector in v.vectors)
                {
                    bool[][] tmp = new bool[2][];
                    tmp[0] = new bool[vector.Value[0].Length];
                    for (int i = 0; i < vector.Value[0].Length; i++)
                    {
                        tmp[0][i] = vector.Value[0][i];
                    }
                    tmp[1] = new bool[vector.Value[1].Length];
                    for (int i = 0; i < vector.Value[1].Length; i++)
                    {
                        tmp[1][i] = vector.Value[1][i];
                    }
                    vectors.Add(vector.Key, tmp);

                }

                SatisfactionLandmarks = new bool[v.SatisfactionLandmarks.Length];
                for (int i = 0; i < v.SatisfactionLandmarks.Length; i++)
                {
                    SatisfactionLandmarks[i] = v.SatisfactionLandmarks[i];
                }
                anyTimeSatisfactionLandmarks = new bool[v.anyTimeSatisfactionLandmarks.Length];
                for (int i = 0; i < v.anyTimeSatisfactionLandmarks.Length; i++)
                {
                    anyTimeSatisfactionLandmarks[i] = v.anyTimeSatisfactionLandmarks[i];
                }
            }
            lastPrivateIndex = v.lastPrivateIndex;
            publicParent = v.publicParent;
            lastPublic = v.lastPublic;
            isComplex = v.isComplex;
            privateActionCounter = v.privateActionCounter;
            h2 = v.h2;
            isPreferable = v.isPreferable;
            if (v.agentsAproxPlan != null)
                agentsAproxPlan = new Dictionary<string, List<Action>>(v.agentsAproxPlan);
            if (v.MemAgentsAproxPlan != null)
                MemAgentsAproxPlan = new Dictionary<string, List<Action>>(v.MemAgentsAproxPlan);
            if (v.goalCost != null)
                goalCost = new Dictionary<GroundedPredicate, KeyValuePair<string, int>>(v.goalCost);
            if (v.othersCourrentState != null)
                othersCourrentState = new Dictionary<string, HashSet<Predicate>>(v.othersCourrentState);
            if (v.relaxPlan != null)
                relaxPlan = v.relaxPlan;
            if (v.projectionPlan != null)
                projectionPlan = v.projectionPlan;
            /*satisfiedVector = new Dictionary<string, bool[]>();
            foreach (var satVec in v.satisfiedVector)
            {
                satisfiedVector.Add(satVec.Key, satVec.Value);
            }*/
            old_h = v.old_h;
            if (Program.highLevelPlanerType == Program.HighLevelPlanerType.Mafsff)
            {
                preferFacts = v.preferFacts;
            }
            if (Program.projectionVersion == Program.ProjectionVersion.ProjectionFF)
            {
                preferFacts = v.preferFacts;
            }
        }
        public MapsVertex PdbAplly(Action action)
        {
            MapsVertex newVertex = new MapsVertex(this);
            
            newVertex.state = newVertex.state.ApplyII(action);
            if (newVertex.state == null)
                return null;
            MapsPlanner.generateCounter++;
            ApplyPublicEffects(action.Effects, newVertex.publicFacts, MapsPlanner.allPublicFacts);
            State newState = new State((Problem)null);

            //newVertex.publicFacts=new HashSet<GroundedPredicate>();
            State partialState = new State((Problem)null);

            foreach (GroundedPredicate gp in newVertex.state.m_lPredicates.ToList())
            {
                if (!MapsPlanner.allPublicFacts.Contains(gp))
                {
                    //newVertex.publicFacts.Add(gp);
                    newState.m_lPredicates.Add(gp);
                }
                else
                {
                    //  Console.WriteLine(gp.ToString());
                }
            }
            int newIndex = mapsAgents[agent].SetPrivateState(newState);
            newVertex.stateIndexes[agent] = newIndex;


            newVertex.g++;
            newVertex.lplan.Add(action);
            if (!action.isPublic)
            {
                //newVertex.lastPrivateIndex = lastPrivateIndex;
                newVertex.lastPublic = lastPublic;
                //newVertex.publicParent = lastPublic;
            }
            else
            {
                //newVertex.publicParent = this;
                newVertex.publicParent = lastPublic;
                newVertex.lastPublic = newVertex;
                //newVertex.lastPrivateIndex = newIndex;
            }

            // newVertex.h2 = newVertex.ComputeFF_h();
            //newVertex.Parent = this;




            foreach (GroundedPredicate pGp in newVertex.publicFacts)
            {
                partialState.m_lPredicates.Add(pGp);
            }

            foreach (var ma in mapsAgents)
            {
                State pState = ma.Value.GetPrivateState(newVertex.stateIndexes[ma.Key]);
                foreach (GroundedPredicate gp in pState.m_lPredicates)
                {
                    partialState.m_lPredicates.Add(gp);
                }
            }
            List<GroundedPredicate> restGoals = new List<GroundedPredicate>();
            foreach (var pair in goalCost)
            {
                if (pair.Value.Value > 0)
                {
                    restGoals.Add(pair.Key);
                }
                else
                {
                    if (action.HashEffects.Contains(pair.Key.Negate()))
                    {
                        restGoals.Add(pair.Key);
                    }
                }
            }
            HashSet<string> relevantAgents = new HashSet<string>();
            relevantAgents.Add(agent);
            if (action.isPublic)
            {
                foreach (MapsAgent a in mapsAgents.Values)
                {
                    bool relevant = false;
                    foreach (GroundedPredicate gp in action.HashEffects)
                    {
                        //if (PublicPredicates.Contains(gp) || PublicPredicates.Contains((GroundedPredicate)gp.Negate()))
                        if (a.publicFacts.Contains(gp))
                        {
                            relevant = true;
                            break;
                        }
                    }
                    if (relevant)
                        relevantAgents.Add(a.name);

                }
            }
            newVertex.goalCost = new Dictionary<GroundedPredicate, KeyValuePair<string, int>>(goalCost);
            newVertex.h = Pdb_h_Calculation(pdb, partialState, newVertex.goalCost, relevantAgents, restGoals);




            newVertex.isComplex = isComplex;
            newVertex.privateActionCounter = privateActionCounter;

            if (clearCounter)
            {
                newVertex.privateActionCounter = 0;
            }
            if (action.isPublic)
            {
                newVertex.clearCounter = true;
            }
            else
            {
                newVertex.privateActionCounter++;
            }
            // newVertex.fromOthers = fromOthers;
            return newVertex;
        }
        public MapsVertex ProjectionAplly(Action action)
        {
            MapsVertex newVertex = new MapsVertex(this);
            newVertex.state = newVertex.state.ApplyII(action);
            if (newVertex.state == null)
                return null;
            MapsPlanner.generateCounter++;
            ApplyPublicEffects(action.Effects, newVertex.publicFacts, MapsPlanner.allPublicFacts);
            State newState = new State((Problem)null);

            //newVertex.publicFacts=new HashSet<GroundedPredicate>();
            //State partialState = new State((Problem)null);

            foreach (GroundedPredicate gp in newVertex.state.m_lPredicates.ToList())
            {
                if (!MapsPlanner.allPublicFacts.Contains(gp))
                {
                    //newVertex.publicFacts.Add(gp);
                    newState.m_lPredicates.Add(gp);
                }
                else
                {
                    //  Console.WriteLine(gp.ToString());
                }
            }
            int newIndex = mapsAgents[agent].SetPrivateState(newState);
            newVertex.stateIndexes[agent] = newIndex;


            newVertex.g++;
            newVertex.lplan.Add(action);
            if (!action.isPublic)
            {
                //newVertex.lastPrivateIndex = lastPrivateIndex;
                newVertex.lastPublic = lastPublic;
                //newVertex.publicParent = lastPublic;
            }
            else
            {
                //newVertex.publicParent = this;
                newVertex.publicParent = lastPublic;
                newVertex.lastPublic = newVertex;
                //newVertex.lastPrivateIndex = newIndex;
            }

            // newVertex.h2 = newVertex.ComputeFF_h();
            //newVertex.Parent = this;

            /* foreach (GroundedPredicate pGp in newVertex.publicFacts)
             {
                 partialState.m_lPredicates.Add(pGp);
             }

             foreach (var ma in mapsAgents)
             {
                 State pState = ma.Value.GetPrivateState(newVertex.stateIndexes[ma.Key]);
                 foreach (GroundedPredicate gp in pState.m_lPredicates)
                 {
                     partialState.m_lPredicates.Add(gp);
                 }
             }*/

            HashSet<string> relevantAgents = new HashSet<string>();
            relevantAgents.Add(agent);
            if (action.isPublic)
            {
                foreach (MapsAgent a in mapsAgents.Values)
                {
                    bool relevant = false;
                    foreach (GroundedPredicate gp in action.HashEffects)
                    {
                        //if (PublicPredicates.Contains(gp) || PublicPredicates.Contains((GroundedPredicate)gp.Negate()))
                        if (a.publicFacts.Contains(gp))
                        {
                            relevant = true;
                            break;
                        }
                    }
                    if (relevant)
                        relevantAgents.Add(a.name);

                }
            }
            //  newVertex.goalCost = new Dictionary<GroundedPredicate, KeyValuePair<string, int>>(goalCost);
            if(othersCourrentState!=null)
                newVertex.othersCourrentState = new Dictionary<string, HashSet<Predicate>>(othersCourrentState);
            newVertex.h = h;



           
            if (Program.projectionVersion == Program.ProjectionVersion.Global || Program.projectionVersion == Program.ProjectionVersion.GlobalV2)
            {
                if (relaxPlan != null && relaxPlan.Count > 0 && (relaxPlan[0].Equals(action.Name) ))
                {
                   // if(!relaxPlan[0].Equals(action.Name) && EqualOnPublicEff(action, MapsVertex.mapsAgents[agent].projectionHeuristic.mapActionNameToAction[relaxPlan[0]], MapsPlanner.allPublicFacts))
                  //      Console.Write("ggg");
                    newVertex.isPreferable = true;
                    newVertex.h = h - 1;
                    newVertex.relaxPlan = new List<string>((IEnumerable<string>)relaxPlan);
                    newVertex.relaxPlan.RemoveAt(0);
                    newVertex.afterMe = afterMe;
                    newVertex.projectionPlan = new List<Action>(projectionPlan);
                   // if (!newVertex.projectionPlan[0].Equals(action))
                    //    Console.Write("ggg");
                    if (action.isPublic)
                        newVertex.projectionPlan.RemoveAt(0);
                }
            
            }           
            else
            if (Program.projectionVersion == Program.ProjectionVersion.fullGlobal)
            {
                if (relaxPlan != null && relaxPlan.Count > 0 && relaxPlan[0].Equals(action.Name))
                {
                    newVertex.isPreferable = true;
                    newVertex.h = h - 1;
                    newVertex.relaxPlan = new List<string>(relaxPlan);
                    newVertex.relaxPlan.RemoveAt(0);
                }
            }
            else
                if (Program.projectionVersion == Program.ProjectionVersion.ProjectionFF)
            {

                foreach (GroundedPredicate gp in action.HashEffects)
                {
                    if (preferFacts.Contains(gp))
                    {
                        newVertex.isPreferable = true;
                    }
                }
            }
            else
            {
                if(Program.highLevelPlanerType == Program.HighLevelPlanerType.Mafsff)
            {
                    foreach (GroundedPredicate gp in action.HashEffects)
                    {
                        if (preferFacts.Contains(gp))
                        {
                            newVertex.isPreferable = true;
                        }
                    }
                }
            }


            newVertex.isComplex = isComplex;
            newVertex.privateActionCounter = privateActionCounter;

            if (clearCounter)
            {
                newVertex.privateActionCounter = 0;
            }
            if (action.isPublic)
            {
                newVertex.clearCounter = true;
            }
            else
            {
                newVertex.privateActionCounter++;
            }
            // newVertex.fromOthers = fromOthers;
            return newVertex;
        }

        public bool EqualOnPublicEff(Action act1,Action act2,HashSet<GroundedPredicate> publicFact)
        {
            if (!act1.isPublic || !act2.isPublic)
                return false;

            List<Predicate> eff1 = act1.HashEffects;
            foreach(GroundedPredicate p in act2.HashEffects)
            {
                if(publicFact.Contains(p))
                {
                    if(!eff1.Contains(p))
                    {
                        return false;
                    }
                }
            }
            return true;
        }
        public int Pdb_h_Calculation(PatternDatabase pdb, State partialState, Dictionary<GroundedPredicate, KeyValuePair<string, int>> goalCost, HashSet<string> relevantAgent, List<GroundedPredicate> restGoals)
        {
            Dictionary<string, Dictionary<GroundedPredicate, int>> agentsDeleteRelaxGraph = new Dictionary<string, Dictionary<GroundedPredicate, int>>();
            // relevantAgent = new HashSet<string>();
            // relevantAgent.Add(agent);
            foreach (MapsAgent a in mapsAgents.Values)
            {
                if (!relevantAgent.Contains(a.name))
                    continue;
                agentsDeleteRelaxGraph.Add(a.name, a.GetRelaxGraph(partialState, restGoals));
            }
            int totalCost = 0;
            foreach (GroundedPredicate goal in allGoals)
            {
                string minCostAgent = null;
                int cost = 1000;
                if (goalCost[goal].Key != null && !relevantAgent.Contains(goalCost[goal].Key))
                {
                    cost = goalCost[goal].Value;
                    minCostAgent = goalCost[goal].Key;
                }
                foreach (var agentGarph in agentsDeleteRelaxGraph)
                {
                    Dictionary<GroundedPredicate, int> relaxGraph = agentGarph.Value;
                    if (relaxGraph.ContainsKey(goal) && relaxGraph[goal] < cost)
                    {
                        cost = relaxGraph[goal];
                        minCostAgent = agentGarph.Key;
                    }
                    if (pdb.cooperationCanGet.ContainsKey(goal))
                    {
                        foreach (var kvp in pdb.cooperationCanGet[goal])
                        {
                            if (relaxGraph.ContainsKey(kvp.Key) && (relaxGraph[kvp.Key] + kvp.Value) < cost)
                            {
                                cost = (relaxGraph[kvp.Key] + kvp.Value);
                                minCostAgent = agentGarph.Key;
                            }
                        }


                    }

                }
                // if (goalCost[goal].Value > cost)
                {
                    goalCost[goal] = new KeyValuePair<string, int>(minCostAgent, cost);
                }
                totalCost += cost;
            }
            return totalCost;
        }
        public int InitGoalCost(PatternDatabase pdb, State partialState)
        {
            goalCost = new Dictionary<GroundedPredicate, KeyValuePair<string, int>>();
            Dictionary<string, Dictionary<GroundedPredicate, int>> agentsDeleteRelaxGraph = new Dictionary<string, Dictionary<GroundedPredicate, int>>();
            foreach (MapsAgent a in mapsAgents.Values)
            {
                agentsDeleteRelaxGraph.Add(a.name, a.GetRelaxGraph(partialState, allGoals.ToList()));
            }
            int totalCost = 0;
            foreach (GroundedPredicate goal in allGoals)
            {
                int cost = 1000;
                string minCostAgent = null;
                foreach (var agentGarph in agentsDeleteRelaxGraph)
                {
                    Dictionary<GroundedPredicate, int> relaxGraph = agentGarph.Value;
                    if (relaxGraph.ContainsKey(goal) && relaxGraph[goal] < cost)
                    {
                        cost = relaxGraph[goal];
                        minCostAgent = agentGarph.Key;
                    }
                    if (pdb.cooperationCanGet.ContainsKey(goal))
                    {
                        foreach (var kvp in pdb.cooperationCanGet[goal])
                        {
                            if (relaxGraph.ContainsKey(kvp.Key) && (relaxGraph[kvp.Key] + kvp.Value) < cost)
                            {
                                cost = (relaxGraph[kvp.Key] + kvp.Value);
                                minCostAgent = agentGarph.Key;
                            }
                        }


                    }

                }

                goalCost[goal] = new KeyValuePair<string, int>(minCostAgent, cost);

                totalCost += cost;
            }
            return totalCost;
        }
        public MapsVertex Aplly(Action action)
        {
            if (Program.highLevelPlanerType == Program.HighLevelPlanerType.PDBMafs)
            {
                return PdbAplly(action);
            }
            if (Program.highLevelPlanerType == Program.HighLevelPlanerType.ProjectionMafs)
            {
                return ProjectionAplly(action);
            }
            if (Program.highLevelPlanerType == Program.HighLevelPlanerType.DistrebutedProjectionMafs)
            {
                return ProjectionAplly(action);
            }
            if (Program.highLevelPlanerType == Program.HighLevelPlanerType.Mafsff)
            {
                return ProjectionAplly(action);
            }

            MapsVertex newVertex = new MapsVertex(this);
            
            // if (action.Name.Equals("MacroAction46"))
            //                          Console.WriteLine("ss");
            if (action is MacroAction)
            {
                MacroAction act = (MacroAction)action;
                foreach (string index in act.preIndex)
                {
                    if (stateIndexes[index] != act.parentIndex[index])
                    {
                        return null;
                    }
                }
                /*newVertex.state = newVertex.state.ApplyIII(act);
                if (newVertex.state == null)
                {
                    return null;
                }*/
                bool canDone = newVertex.state.CanDone(act);
                if (!canDone)
                {
                    return null;
                }
                MapsPlanner.generateCounter++;
                newVertex.fullCopy(this);
                // if(act.preIndex.Contains(agent) && agent.Equals("Agent: 0"))
                //    Console.WriteLine("***");
                foreach (string index in act.preIndex)
                {
                    newVertex.stateIndexes[index] = act.childIndex[index];
                }


                /*state = new State(mapsAgents[agent].GetPrivateState(stateIndexes[agent]));
                foreach (GroundedPredicate gp in publicFacts)
                {
                    state.AddPredicate(gp);
                }*/

                ApplyPublicEffects2(action.HashEffects, newVertex.publicFacts, MapsPlanner.allPublicFacts);

                newVertex.state = new State(mapsAgents[agent].GetPrivateState(newVertex.stateIndexes[agent]));
                foreach (GroundedPredicate gp in newVertex.publicFacts)
                {
                    newVertex.state.AddPredicate(gp);
                }
                newVertex.g = +act.cost;
                // newVertex.lplan.Add(new Action("-----------------start---------------"));
                //foreach (Action microActions in act.microActions)
                // {
                //     newVertex.lplan.Add(microActions);

                // }
                //newVertex.lplan.Add(new Action("-----------------end---------------"));
                newVertex.lplan.Add(action);
                // newVertex.publicParent = lastPublic;
                newVertex.lastPublic = lastPublic;
                //  newVertex.lastPublic = newVertex;
                //string agnt = act.agent;
                foreach (string agnt in mapsAgents.Keys)// act.preIndex)
                {
                    for (int i = 0; i < newVertex.vectors[agnt][0].Length; i++)
                    {
                        if (act.landmarkVector[i])
                        {
                            newVertex.vectors[agnt][0][i] = true;
                        }
                        if (act.NeglandmarkVector[i])
                        {
                            newVertex.vectors[agnt][0][i] = false;
                        }

                    }
                    for (int i = 0; i < newVertex.vectors[agnt][1].Length; i++)
                    {
                        if (act.rOrder[i])
                        {
                            newVertex.vectors[agnt][1][i] = true;
                        }
                    }
                    /* bool[] newSat = new bool[satisfiedVector[agnt].Length];
                     for (int i = 0; i < satisfiedVector[agnt].Length; i++)
                     {
                         if (satisfiedVector[agnt][i] && !act.negSatNowVectors[agnt][i])
                         {
                             newSat[i] = true;
                         }
                         else
                         {
                             if (act.satNowVectors[agnt][i])
                             {
                                 newSat[i] = true;
                             }
                         }
                        
                     }

                     newVertex.satisfiedVector[agnt] = newSat;*/
                }
                for (int i = 0; i < newVertex.vectors.First().Value[0].Length; i++)
                {
                    if (act.landmarkVector[i])
                    {
                        newVertex.SatisfactionLandmarks[i] = true;
                    }
                    if (act.NeglandmarkVector[i])
                    {
                        newVertex.SatisfactionLandmarks[i] = false;
                    }
                    if (act.anyTimeVector[i])
                    {
                        newVertex.anyTimeSatisfactionLandmarks[i] = true;
                    }
                }
                newVertex.h = 0;
                foreach (bool sat in newVertex.SatisfactionLandmarks)
                {
                    if (!sat)
                        newVertex.h++;
                }
                newVertex.isComplex = true;
                newVertex.privateActionCounter = privateActionCounter;
                if (clearCounter)
                {
                    newVertex.privateActionCounter = 0;
                }
                //newVertex.satisfiedVector = satisfiedVector;
                // newVertex.h2 = newVertex.ComputeFF_h();
                newVertex.isComplex = true;
                //newVertex.fromOthers = fromOthers;
                return newVertex;
            }
            else
            {
                newVertex.state = newVertex.state.ApplyII(action);
                if (newVertex.state == null)
                    return null;
                MapsPlanner.generateCounter++;
                ApplyPublicEffects(action.Effects, newVertex.publicFacts, MapsPlanner.allPublicFacts);
                State newState = new State((Problem)null);

                //newVertex.publicFacts=new HashSet<GroundedPredicate>();

                foreach (GroundedPredicate gp in newVertex.state.m_lPredicates.ToList())
                {
                    if (!MapsPlanner.allPublicFacts.Contains(gp))
                    {
                        //newVertex.publicFacts.Add(gp);
                        newState.m_lPredicates.Add(gp);
                    }
                    else
                    {
                        //  Console.WriteLine(gp.ToString());
                    }
                }
                int newIndex = mapsAgents[agent].SetPrivateState(newState);
                newVertex.stateIndexes[agent] = newIndex;


                newVertex.g++;
                newVertex.lplan.Add(action);
                if (!action.isPublic)
                {
                    //newVertex.lastPrivateIndex = lastPrivateIndex;
                    newVertex.lastPublic = lastPublic;
                    //newVertex.publicParent = lastPublic;
                }
                else
                {
                    //newVertex.publicParent = this;
                    newVertex.publicParent = lastPublic;
                    newVertex.lastPublic = newVertex;
                    //newVertex.lastPrivateIndex = newIndex;
                }
                int newH = 0;
                List<bool[]> vectors = new List<bool[]>();
                List<bool[]> vectors2 = new List<bool[]>();
                //newVertex.satisfiedVector = new Dictionary<string, bool[]>();
                Dictionary<string, bool[][]> newVectors = new Dictionary<string, bool[][]>();

                for (int i = 0; i < mapsAgents.Count; i++)
                {
                    bool[] satisfiedNew = null;
                    bool[][] ans = null;
                    if (mapsAgents.ElementAt(i).Key.Equals(agent))
                    {
                        ans = mapsAgents.ElementAt(i).Value.Geth(newVertex.state, out satisfiedNew, this.vectors.ElementAt(i).Value[0], this.vectors.ElementAt(i).Value[1]);
                        //newVertex.satisfiedVector.Add(agent, satisfiedNew);  
                    }
                    else
                    {
                        var a = mapsAgents.ElementAt(i);
                        State tmpState = new State(a.Value.GetPrivateState(stateIndexes[a.Key]));
                        foreach (GroundedPredicate gp in newVertex.publicFacts)
                        {
                            tmpState.AddPredicate(gp);
                        }
                        ans = mapsAgents.ElementAt(i).Value.Geth(tmpState, out satisfiedNew, this.vectors.ElementAt(i).Value[0], this.vectors.ElementAt(i).Value[1]);
                        //newVertex.satisfiedVector.Add(this.vectors.ElementAt(i).Key, satisfiedVector[this.vectors.ElementAt(i).Key]);
                        /*  try
                          {
                         ans = this.vectors.ElementAt(i).Value;

                         newVertex.satisfiedVector.Add(this.vectors.ElementAt(i).Key, satisfiedVector[this.vectors.ElementAt(i).Key]);
                         satisfiedNew =  newVertex.satisfiedVector[this.vectors.ElementAt(i).Key];
                          }
                          catch (Exception ex)
                          {
                              Console.WriteLine("ddd");
                          }*/
                    }
                    newVectors.Add(mapsAgents.ElementAt(i).Key, ans);
                    vectors.Add(ans[0]);
                    vectors2.Add(satisfiedNew);
                }



                bool[] firstVector = new bool[vectors.ElementAt(0).Length];
                bool[] secondVector = new bool[vectors.ElementAt(0).Length];
                for (int j = 0; j < firstVector.Length; j++)
                {

                    bool flag = false;
                    foreach (var vector in vectors)
                    {
                        if (vector[j] == true)
                        {
                            flag = true;
                            firstVector[j] = true;
                            // if (oldVector[j] == false)
                            //  innovative = true;
                            break;
                        }
                    }
                    foreach (var vector2 in vectors2)
                    {
                        if (vector2[j] == true)
                        {
                            flag = true;
                            secondVector[j] = true;
                            break;
                        }
                    }



                }
                bool[] tmpAntTime = new bool[firstVector.Length];
                for (int j = 0; j < firstVector.Length; j++)
                {

                    if (firstVector[j] || this.anyTimeSatisfactionLandmarks[j])
                    {
                        tmpAntTime[j] = true;
                    }

                }
                //h2 += makeFalse;
                bool f = true;
                // not using Orders
                while (f)
                {
                    f = false;
                    foreach (PPOrder order in Distributed_Landmarks_Detection.necessaryPPOrders)
                    {
                        if (firstVector[order.lendmark1.index] && !secondVector[order.lendmark1.index] && !tmpAntTime[order.lendmark2.index])
                        {
                            firstVector[order.lendmark1.index] = false;
                            f = true;
                            for (int i = 0; i < newVectors.Count; i++)
                            {
                                newVectors.ElementAt(i).Value[0][order.lendmark1.index] = false;
                            }
                        }
                    }
                }
                //int makeFalse = 0;
                //  List<int> indexes = new List<int>(indexsOfLandmarks);

                for (int j = 0; j < firstVector.Length; j++)
                {
                    /*if (!firstVector[j] && SatisfactionLandmarks[j])
                    {
                        if (!indexes.Contains(j))
                            indexes.Add(j);
                    }*/
                    if (!firstVector[j])
                    {
                        newH++;
                    }
                }
                newVertex.h = newH;
                // newVertex.h2 = newVertex.ComputeFF_h();
                //newVertex.Parent = this;
                newVertex.vectors = newVectors;
                newVertex.SatisfactionLandmarks = firstVector;
                newVertex.anyTimeSatisfactionLandmarks = tmpAntTime;
                newVertex.isComplex = isComplex;
                newVertex.privateActionCounter = privateActionCounter;
                if (clearCounter)
                {
                    newVertex.privateActionCounter = 0;
                }
                if (action.isPublic)
                {
                    newVertex.clearCounter = true;
                }
                else
                {
                    newVertex.privateActionCounter++;
                }
                // newVertex.fromOthers = fromOthers;
                return newVertex;
            }
        }
        public int GetProjection_h()
        {
            if (Program.projectionVersion == Program.ProjectionVersion.Local)
            {
                return GetProjection_h1();
            }            
            if (Program.projectionVersion == Program.ProjectionVersion.Global)
            {
                return GetProjection_h2();
            }
            if (Program.projectionVersion == Program.ProjectionVersion.ProjectionFF)
            {
                return GetProjectionFF();
            }
            if (Program.projectionVersion == Program.ProjectionVersion.fullGlobal)
            {
                return GetProjection_hFull();
            }
            if (Program.projectionVersion == Program.ProjectionVersion.GlobalV2)
            {
                return GetProjection_GlobalV2();
            }
            throw new Exception();
        }
        public int GetProjection_h1()
        {
            h = 0;
            List<HashSet<Predicate>> listOfState = new List<HashSet<Predicate>>();
            Dictionary<string, List<Action>> localPlans = new Dictionary<string, List<Action>>();
            State myState = new State((Problem)null);
            foreach (var ma in mapsAgents)
            {
                localPlans.Add(ma.Key, new List<Action>());
                HashSet<Predicate> courrentState = new HashSet<Predicate>();

                State pState = ma.Value.GetPrivateState(stateIndexes[ma.Key]);
                foreach (Predicate gp in pState.m_lPredicates)
                {
                    courrentState.Add(gp);
                }
                HashSet<Predicate> aproxState = null;
                if (ma.Key.Equals(agent))
                {
                    foreach (Predicate pGp in publicFacts)
                    {
                        courrentState.Add(pGp);
                    }
                    foreach (GroundedPredicate gp in courrentState)
                    {
                        myState.AddPredicate(gp);
                    }
                    aproxState = agents[ma.Key].GetPublicStartState(courrentState, ma.Value.WhatICanGet(courrentState));

                    listOfState.Add(aproxState);


                }
                else
                {

                    if (othersCourrentState.ContainsKey(ma.Key))
                    {
                        aproxState = othersCourrentState[ma.Key];
                    }
                    else
                    {
                        aproxState = agents[ma.Key].GetPublicStartState(courrentState, ma.Value.WhatICanGet(courrentState));
                        othersCourrentState.Add(ma.Key, aproxState);
                    }


                    listOfState.Add(aproxState);
                }

            }
            //localPlan = new List<Action>();
            List<Action> allAproxPlan = new List<Action>();
            int hsp;
            int flag = mapsAgents[agent].projectionHeuristic.GethValue2(agents[agent], listOfState, localPlans, allAproxPlan,out hsp);
            if (flag == -1)
            {
                Console.WriteLine("didn't find projection plan ");
                h = 1000 + hsp;
                return h;
            }

            localPlan = RegGrounding(myState, allAproxPlan, out h);
            return h;
        }

        static int countChack = 0;
        public int GetProjection_h4()
        {
            // countChack++;
            //  Console.WriteLine(countChack);
            h = 0;
            agentsAproxPlan = new Dictionary<string, List<Action>>();
            foreach (var firstAgent in mapsAgents.Values)
            {
                List<HashSet<Predicate>> listOfState = new List<HashSet<Predicate>>();
                foreach (var ma in mapsAgents)
                {
                    HashSet<Predicate> courrentState = new HashSet<Predicate>();

                    State pState = ma.Value.GetPrivateState(stateIndexes[ma.Key]);
                    foreach (Predicate gp in pState.m_lPredicates)
                    {
                        courrentState.Add(gp);
                    }
                    if (ma.Key.Equals(firstAgent.name))
                    {
                        foreach (Predicate pGp in publicFacts)
                        {
                            courrentState.Add(pGp);
                        }
                        listOfState.Add(courrentState);
                    }
                    else
                    {
                        HashSet<Predicate> aproxState = null;
                        if (othersCourrentState.ContainsKey(ma.Key))
                        {
                            aproxState = othersCourrentState[ma.Key];
                        }
                        else
                        {
                            aproxState = agents[ma.Key].GetPublicStartState(courrentState, ma.Value.WhatICanGet(courrentState));
                            if (false && !ma.Key.Equals(agent))
                                othersCourrentState.Add(ma.Key, aproxState);
                        }
                        listOfState.Add(aproxState);

                    }
                }
                agentsAproxPlan[firstAgent.name] = new List<Action>();
                int agent_h = mapsAgents[firstAgent.name].projectionHeuristic.GethValue(agents[firstAgent.name], listOfState, false, agentsAproxPlan[firstAgent.name]);
                h += agent_h;
            }

            return h;
        }
        public List<Action> fflPlan = null;
        int old_h = 0;
        public int GetProjectionFF()
        {
            old_h = h;
            h = 0;
            preferFacts = new HashSet<GroundedPredicate>();
            HashSet<Predicate> aproxState = GetAproxState();
            Dictionary<Predicate, Action> firstAchievers = FindFirstAchievers(aproxState);
            fflPlan = new List<Action>();
            HashSet<Predicate> needToAchieve = new HashSet<Predicate>(agentsGoals);
            HashSet<Predicate> alreadyAchieved = new HashSet<Predicate>();
            bool deadEnd = false;
            bool stop = false;
            while(!stop)
            {
                stop = true;
                HashSet<Predicate> tmpSet = new HashSet<Predicate>();
                foreach(Predicate p in needToAchieve)
                {
                    if (firstAchievers.ContainsKey(p))
                    {
                        Action act = firstAchievers[p];
                        if (act != null)
                        {
                            if (!fflPlan.Contains(act))
                            {
                                fflPlan.Insert(0, act);
                                h++;
                                foreach (Predicate pre in act.HashPrecondition)
                                {
                                    tmpSet.Add(pre);
                                }
                            }
                            preferFacts.Add((GroundedPredicate)p);
                        }
                        alreadyAchieved.Add(p);
                    }
                    else
                    {
                        deadEnd = true;
                        h += 1000;
                    }                    
                }
                needToAchieve = new HashSet<Predicate>();
                foreach (Predicate nextLavelP in tmpSet)
                {
                    if (!alreadyAchieved.Contains(nextLavelP))
                    {
                        needToAchieve.Add(nextLavelP);
                        stop = false;
                    }
                }
            }

            return h;
        }
        public bool useRegularPrivateAction = false;
        public Dictionary<Predicate,Action> FindFirstAchievers(HashSet<Predicate> m_aproxState)
        {
            HashSet<Predicate> aproxState = m_aproxState;
            Dictionary<Predicate, Action> firstAchievers = new Dictionary<Predicate, Action>();
            foreach(GroundedPredicate sGp in aproxState)
            {
                firstAchievers.Add(sGp, null);
            }
            List<Action> privateActions = mapsAgents[agent].privateActions;
            List<Action> publicActions = mapsAgents[agent].projectionHeuristic.allProjectionAction;
            if(useRegularPrivateAction)
            {
                publicActions.AddRange(mapsAgents[agent].privateActions);
            }

            bool stop = false;
            HashSet<Predicate> addsFacts = null;
            while (!stop)
            {
                stop = true;
                addsFacts = new HashSet<Predicate>();
                bool stopPrivate = false;
                if (!useRegularPrivateAction)
                {
                    while (!stopPrivate)
                    {
                        stopPrivate = true;
                        foreach (Action privatAct in privateActions)
                        {
                            if (Contains(aproxState, privatAct.HashPrecondition))
                            {
                                foreach (Predicate p in privatAct.HashEffects)
                                {
                                    if (!aproxState.Contains(p) && !addsFacts.Contains(p))
                                    {
                                        addsFacts.Add(p);
                                        stopPrivate = false;
                                        firstAchievers.Add((GroundedPredicate)p, privatAct);
                                    }
                                }
                            }
                        }
                        if (addsFacts.Count > 0)
                        {
                            foreach (Predicate p in addsFacts)
                            {
                                aproxState.Add(p);
                            }
                            addsFacts = new HashSet<Predicate>();
                        }
                    }
                }
                foreach (Action publicAct in publicActions)
                {
                    if (Contains(aproxState, publicAct.HashPrecondition))
                    {
                        foreach (Predicate p in publicAct.HashEffects)
                        {
                            if (!aproxState.Contains(p) && !addsFacts.Contains(p))
                            {
                                addsFacts.Add(p);
                                stop = false;
                                firstAchievers.Add((GroundedPredicate)p, publicAct);
                            }
                        }
                    }
                }
                if (addsFacts.Count > 0)
                {
                    foreach (Predicate p in addsFacts)
                    {
                        aproxState.Add(p);
                    }
                }
                if (Contains(aproxState, agentsGoals))
                {
                    stop = true;
                }

            }
            return firstAchievers;
        }
        
        public HashSet<Predicate> GetAproxState()
        {
            HashSet<Predicate> aproxState = new HashSet<Predicate>();
            HashSet<Predicate> courrentState2 = null;
            foreach (KeyValuePair<string, MapsAgent> keyValuePair in MapsVertex.mapsAgents)
            {
               
                if (keyValuePair.Key.Equals(agent))
                {
                    aproxState.UnionWith(state.m_lPredicates);
                }
                else
                {
                    
                    HashSet<Predicate> hashSet;
                    if (othersCourrentState.ContainsKey(keyValuePair.Key))
                        hashSet = othersCourrentState[keyValuePair.Key];
                    else
                    {
                        courrentState2 = new HashSet<Predicate>();
                        foreach (Predicate predicate in keyValuePair.Value.GetPrivateState(stateIndexes[keyValuePair.Key]).m_lPredicates)
                        {
                            courrentState2.Add(predicate);
                        }
                        foreach (Predicate predicate in publicFacts)
                        {
                            courrentState2.Add(predicate);
                        }
                        hashSet = MapsVertex.agents[keyValuePair.Key].GetPublicStartState(courrentState2, keyValuePair.Value.WhatICanGet(courrentState2));
                        HashSet<Predicate> privateStartState = new HashSet<Predicate>();
                        foreach(Predicate p in hashSet)
                        {
                            if (!keyValuePair.Value.publicFacts.Contains((GroundedPredicate)p))
                                privateStartState.Add(p);
                        }
                        othersCourrentState.Add(keyValuePair.Key, privateStartState);
                    }
                    aproxState.UnionWith(hashSet);
                }
            }
            return aproxState;
        }

        public bool Contains(HashSet<Predicate> set,List<Predicate> subSet)
        {
            foreach(Predicate p in subSet)
            {
                if (!set.Contains(p))
                    return false;
            }
            return true;
        }
        public bool Contains(HashSet<Predicate> set, HashSet<Predicate> subSet)
        {
            foreach (Predicate p in subSet)
            {
                if (!set.Contains(p))
                    return false;
            }
            return true;
        }

        public int GetProjection_h2()
        {
            h = 0;
            State courrentState1 = new State((Problem)null);
            agentsAproxPlan = new Dictionary<string, List<Action>>();

            foreach (MapsAgent mapsAgent in MapsVertex.mapsAgents.Values)
                agentsAproxPlan.Add(mapsAgent.name, new List<Action>());

            List<HashSet<Predicate>> states = new List<HashSet<Predicate>>();

            foreach (KeyValuePair<string, MapsAgent> keyValuePair in MapsVertex.mapsAgents)
            {
                HashSet<Predicate> courrentState2 = new HashSet<Predicate>();
                foreach (Predicate predicate in keyValuePair.Value.GetPrivateState(stateIndexes[keyValuePair.Key]).m_lPredicates)
                {
                    courrentState2.Add(predicate);
                }
                foreach (Predicate predicate in publicFacts)
                {
                    courrentState2.Add(predicate);
                }
                if (keyValuePair.Key.Equals(agent))
                {
                    
                    foreach (GroundedPredicate groundedPredicate in courrentState2)
                        courrentState1.AddPredicate((Predicate)groundedPredicate);
                    HashSet<Predicate> publicStartState = MapsVertex.agents[keyValuePair.Key].GetPublicStartState(courrentState2, keyValuePair.Value.WhatICanGet(courrentState2));
                    states.Add(publicStartState);
                }
                else
                {
                    HashSet<Predicate> hashSet;
                    if (othersCourrentState.ContainsKey(keyValuePair.Key))
                        hashSet = othersCourrentState[keyValuePair.Key];
                    else
                        hashSet = MapsVertex.agents[keyValuePair.Key].GetPublicStartState(courrentState2, keyValuePair.Value.WhatICanGet(courrentState2));
                    states.Add(hashSet);
                }
            }
            List<Action> list = new List<Action>();
            int hsp;
            if (MapsVertex.mapsAgents[agent].projectionHeuristic.GethValue2(MapsVertex.agents[agent], states, agentsAproxPlan, list, out hsp) == -1)
            {
                Console.WriteLine("didn't find projection plan ");
                h = 1000 + hsp;
                return h;
            }
            projectionPlan = list;
            Dictionary<int, List<string>> groupPlan = new Dictionary<int, List<string>>();
            for (int key = 0; key < list.Count + 1; ++key)
                groupPlan.Add(key, (List<string>)null);
            int actionCount;
            int allActionCount;
            agentsAproxPlan[agent] = MapsVertex.mapsAgents[agent].Grounding(0, courrentState1, list, out actionCount, out allActionCount, groupPlan);
            h = allActionCount;
            relaxPlan = new List<string>();
            int index;
            for (index = 0; index < list.Count && list[index].agent.Equals(agent); ++index)
                relaxPlan.AddRange(groupPlan[index]);
            if (index == list.Count)
                relaxPlan.AddRange(groupPlan[index]);
            else
                afterMe = list[index].agent;
            return h;
        }
        public int GetProjection_GlobalV2()
        {
            h = 0;
            State courrentState1 = new State((Problem)null);
            agentsAproxPlan = new Dictionary<string, List<Action>>();

            foreach (MapsAgent mapsAgent in MapsVertex.mapsAgents.Values)
                agentsAproxPlan.Add(mapsAgent.name, new List<Action>());

            List<HashSet<Predicate>> states = new List<HashSet<Predicate>>();

            foreach (KeyValuePair<string, MapsAgent> keyValuePair in MapsVertex.mapsAgents)
            {
                HashSet<Predicate> courrentState2 = new HashSet<Predicate>();
                foreach (Predicate predicate in keyValuePair.Value.GetPrivateState(stateIndexes[keyValuePair.Key]).m_lPredicates)
                {
                    courrentState2.Add(predicate);
                }
                foreach (Predicate predicate in publicFacts)
                {
                    courrentState2.Add(predicate);
                }
                if (keyValuePair.Key.Equals(agent))
                {

                    foreach (GroundedPredicate groundedPredicate in courrentState2)
                        courrentState1.AddPredicate((Predicate)groundedPredicate);
                    states.Add(courrentState2);
                }
                else
                {
                    HashSet<Predicate> hashSet;
                    if (othersCourrentState.ContainsKey(keyValuePair.Key))
                        hashSet = othersCourrentState[keyValuePair.Key];
                    else
                        hashSet = MapsVertex.agents[keyValuePair.Key].GetPublicStartState(courrentState2, keyValuePair.Value.WhatICanGet(courrentState2));
                    states.Add(hashSet);
                }
            }
            List<Action> list = new List<Action>();
            int hsp;
            if (MapsVertex.mapsAgents[agent].projectionHeuristic.GethValue2(MapsVertex.agents[agent], states, agentsAproxPlan, list, out hsp) == -1)
            {
                Console.WriteLine("didn't find projection plan ");
                h = 1000 + hsp;
                return h;
            }
            projectionPlan = list;

            h = list.Count;
            relaxPlan = new List<string>();
            int index;
            for (index = 0; index < list.Count && list[index].agent.Equals(agent); ++index)
            {
                relaxPlan.Add(list[index].Name);
            }
            for(int i=0;i<list.Count;i++)
            {
                if(!list[i].isPublic)
                {
                    list.RemoveAt(i);
                    i--;
                }
            }        
            if(list.Count>index)
                afterMe = list[index].agent;
            return h;
        }
        public int FindLocalPlan()
        {
            State courrentState1 = new State((Problem)null);

            foreach (GroundedPredicate gp in state.m_lPredicates)
                courrentState1.AddPredicate(gp);
            foreach(GroundedPredicate gp in publicFacts)
                courrentState1.AddPredicate(gp);

            List<Action> list = projectionPlan;
            Dictionary<int, List<string>> groupPlan = new Dictionary<int, List<string>>();
            for (int key = 0; key < list.Count + 1; ++key)
                groupPlan.Add(key, (List<string>)null);
            int actionCount;
            int allActionCount;
            MapsVertex.mapsAgents[agent].Grounding(0, courrentState1, list, out actionCount, out allActionCount, groupPlan);
            h = allActionCount;
            relaxPlan = new List<string>();
            int index;

            for (index = 0; index < list.Count && list[index].agent.Equals(agent); ++index)
            {
                relaxPlan.AddRange(groupPlan[index]);
            }
            if (index == list.Count)
                relaxPlan.AddRange(groupPlan[index]);
            else
                afterMe = list[index].agent;
            return h;
        }
        public int GetProjection_hFull()
        {
            h = 0;
            Dictionary<string, State> dictionary = new Dictionary<string, State>();
            agentsAproxPlan = new Dictionary<string, List<Action>>();
            foreach (MapsAgent mapsAgent in MapsVertex.mapsAgents.Values)
                agentsAproxPlan.Add(mapsAgent.name, new List<Action>());
            List<HashSet<Predicate>> states = new List<HashSet<Predicate>>();
            foreach (KeyValuePair<string, MapsAgent> keyValuePair in MapsVertex.mapsAgents)
            {
                dictionary.Add(keyValuePair.Key, new State((Problem)null));
                HashSet<Predicate> courrentState = new HashSet<Predicate>();
                foreach (Predicate p in keyValuePair.Value.GetPrivateState(stateIndexes[keyValuePair.Key]).m_lPredicates)
                {
                    courrentState.Add(p);
                    dictionary[keyValuePair.Key].AddPredicate(p);
                }
                foreach (Predicate p in publicFacts)
                {
                    dictionary[keyValuePair.Key].AddPredicate(p);
                    courrentState.Add(p);
                }
                if (keyValuePair.Key.Equals(agent))
                {
                    HashSet<Predicate> publicStartState = MapsVertex.agents[keyValuePair.Key].GetPublicStartState(courrentState, keyValuePair.Value.WhatICanGet(courrentState));
                    states.Add(publicStartState);
                }
                else
                {
                    HashSet<Predicate> hashSet;
                    if (othersCourrentState.ContainsKey(keyValuePair.Key))
                        hashSet = othersCourrentState[keyValuePair.Key];
                    else
                        hashSet = MapsVertex.agents[keyValuePair.Key].GetPublicStartState(courrentState, keyValuePair.Value.WhatICanGet(courrentState));
                    states.Add(hashSet);
                }
            }
            List<Action> list = new List<Action>();
            int hsp;
            if (MapsVertex.mapsAgents[agent].projectionHeuristic.GethValue2(MapsVertex.agents[agent], states, agentsAproxPlan, list, out hsp) == -1)
            {
                Console.WriteLine("didn't find projection plan ");
                h = 1000 + hsp;
                return h;
            }
            Dictionary<int, List<string>> groupPlan = new Dictionary<int, List<string>>();
            for (int key = 0; key < list.Count + MapsVertex.agents.Count; ++key)
                groupPlan.Add(key, (List<string>)null);
            int agentIndex = 0;
            foreach (MapsAgent mapsAgent in MapsVertex.mapsAgents.Values)
            {
                int actionCount;
                int allActionCount;
                agentsAproxPlan[mapsAgent.name] = mapsAgent.Grounding(agentIndex, dictionary[mapsAgent.name], list, out actionCount, out allActionCount, groupPlan);
                h = h + actionCount;
                ++agentIndex;
            }
            relaxPlan = new List<string>();
            for (int index = 0; index < list.Count + MapsVertex.agents.Count; ++index)
                relaxPlan.AddRange(groupPlan[index]);
            return h;
        }

        public List<Action> RegGrounding(State courrentState, List<Action> highLevelplan, out int actionCount)
        {
            //  Console.WriteLine("\nPublic global plan found, searching for private plans");
            actionCount = 0;
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
            foreach (Action act in highLevelplan)
            {
                CompoundFormula effect = new CompoundFormula("and");
                bool flag = false;
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (agents[act.agent].PublicPredicates.Contains(gp))
                    {
                        effect.AddOperand(gp);
                        flag = true;
                    }
                }
                if (flag)
                    lplan.Add(new KeyValuePair<string, CompoundFormula>(act.agent, effect));
                else
                    actionCount++;
            }
            int count = 0;
            List<Action> finalPlan = new List<Action>();

            int level = 0;

            CompoundFormula goalFormula = new CompoundFormula("and");
            string agentName;
            foreach (KeyValuePair<string, CompoundFormula> eff in lplan)
            {
                agentName = eff.Key;
                goalFormula = new CompoundFormula(eff.Value);
                if (agent.Equals(agentName))
                {
                    bool bUnsolvable = false;
                    //  ExternalPlanners externalPlanners = new ExternalPlanners();
                    //  List<string> ffLplan = externalPlanners.Plan(true,false,agents[agentName].domain, agents[agentName].problem, courrentState, goalFormula, agents[agentName].m_actions, 5 * 60 * 1000, out bUnsolvable);

                    HSPHeuristic hsp = new HSPHeuristic(agents[agentName].m_actions, goalFormula.GetAllPredicates().ToList(), false);
                    ForwardSearchPlanner forwardSearch = new ForwardSearchPlanner(agents[agentName].m_actions, hsp);
                    List<Action> path = forwardSearch.Plan(courrentState, goalFormula.GetAllPredicates().ToList());
                    List<string> ffLplan = new List<string>();
                    foreach (Action act in path)
                    {
                        ffLplan.Add(act.Name);
                    }
                    if (ffLplan != null)
                    {
                        List<string> todo = ffLplan;
                        foreach (string act in todo)
                        {
                            actionCount++;
                            State s = courrentState.ApplyII(agents[agentName].domain.mapActionNameToAction[act]);
                            if (s == null)
                                throw new Exception();
                            courrentState = s;
                            finalPlan.Add(agents[agentName].domain.mapActionNameToAction[act]);
                        }

                    }
                    else
                    {
                        Program.KillPlanners();
                    }
                }
                else
                {
                    actionCount++;
                    courrentState = courrentState.ApplyEffect(goalFormula, agents[agent].PublicPredicates);
                }
            }
            return finalPlan;
        }
        public List<Action> RegGroundingFF(State courrentState, List<Action> highLevelplan, out int actionCount)
        {
            //  Console.WriteLine("\nPublic global plan found, searching for private plans");
            actionCount = 0;
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
            foreach (Action act in highLevelplan)
            {
                CompoundFormula effect = new CompoundFormula("and");
                bool flag = false;
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (agents[act.agent].PublicPredicates.Contains(gp))
                    {
                        effect.AddOperand(gp);
                        flag = true;
                    }
                }
                if (flag)
                    lplan.Add(new KeyValuePair<string, CompoundFormula>(act.agent, effect));
                else
                    actionCount++;
            }
            int count = 0;
            List<Action> finalPlan = new List<Action>();

            int level = 0;

            CompoundFormula goalFormula = new CompoundFormula("and");
            string agentName;
            foreach (KeyValuePair<string, CompoundFormula> eff in lplan)
            {
                agentName = eff.Key;
                goalFormula = new CompoundFormula(eff.Value);
                if (agent.Equals(agentName))
                {
                    bool bUnsolvable = false;
                    ExternalPlanners externalPlanners = new ExternalPlanners();
                    List<string> ffLplan = externalPlanners.Plan(true, false, agents[agentName].domain, agents[agentName].problem, courrentState, goalFormula, agents[agentName].m_actions, 5 * 60 * 1000, out bUnsolvable);


                    if (ffLplan != null)
                    {
                        List<string> todo = ffLplan;
                        foreach (string act in todo)
                        {
                            actionCount++;
                            State s = courrentState.ApplyII(agents[agentName].domain.mapActionNameToAction[act]);
                            if (s == null)
                                throw new Exception();
                            courrentState = s;
                            finalPlan.Add(agents[agentName].domain.mapActionNameToAction[act]);
                        }

                    }
                    else
                    {
                        Program.KillPlanners();
                    }
                }
                else
                {
                    actionCount++;
                    courrentState = courrentState.ApplyEffect(goalFormula, agents[agent].PublicPredicates);
                }
            }
            return finalPlan;
        }
        public void relaxActions(List<Action> allActions, List<Action> macroActions)
        {
            for (int i = 0; i < macroActions.Count; i++)
            {
                if (macroActions[i] is MacroAction)
                {
                    relaxActions(allActions, ((MacroAction)macroActions[i]).microActions);
                }
                else
                {
                    allActions.Add(macroActions[i]);
                }
            }
        }
        public List<MapsAgent> GetOrderMafsAgents(Dictionary<string,MapsAgent> agents)
        {
            List<MapsAgent> orderList = new List<MapsAgent>();
            orderList.Add(agents[agent]);
            foreach (var mp in agents)
            {
                if (mp.Key.Equals(agent))
                    continue;
                orderList.Add(mp.Value);
            }
            return orderList;
        }
        public List<MapsAgent> GetReverseOrderMafsAgents(Dictionary<string, MapsAgent> agents)
        {
            List<MapsAgent> orderList = new List<MapsAgent>();
            foreach (var mp in agents)
            {
                orderList.Insert(0,mp.Value);
            }
            return orderList;
        }
        public int ComputeFF_h()
        {
            old_h = h;
            HashSet<GroundedPredicate> publicSet = new HashSet<GroundedPredicate>();
            HashSet<GroundedPredicate> tmpPublicSet = new HashSet<GroundedPredicate>();
            List<MapsAgent> agents = mapsAgents.Values.ToList();
            // List<MapsAgent> agents = GetOrderMafsAgents(mapsAgents);
           //  List<MapsAgent> agents = GetReverseOrderMafsAgents(mapsAgents);

            foreach (MapsAgent agent in agents)
            {
                State s = new State(agent.GetPrivateState(stateIndexes[agent.name]));
                foreach (GroundedPredicate gp in publicFacts)
                {
                    s.AddPredicate(gp);
                }
                HashSet<GroundedPredicate> tmp = agent.InitHspGraph(s);
                
                foreach (var gp in tmp)
                {
                    if (!publicSet.Contains(gp))
                    {
                        publicSet.Add(gp);
                    }
                }
                Program.ffMessageCounter++;
            }

            bool flag2 = true;
            int level = 2;
            bool isGlobalGoal=false;
            while (flag2)
            {
                flag2 = false;
                isGlobalGoal = true; ;
                foreach (MapsAgent agent in agents)
                {                  
                    bool isLocalGoal;
                    KeyValuePair<bool, HashSet<GroundedPredicate>> tmp = agent.UpdateHspGraph(publicSet, level, out isLocalGoal);
                    if (!isLocalGoal)
                    {
                        isGlobalGoal = false;
                    }
                    if (tmp.Key == true)
                        flag2 = true;
                    foreach (var gp in tmp.Value)
                    {
                        if (!publicSet.Contains(gp))
                        {
                            tmpPublicSet.Add(gp);
                        }
                    }
                    Program.ffMessageCounter++;
                }
                if (isGlobalGoal)
                {
                    flag2 = false;
                }
                else
                {
                    foreach (GroundedPredicate addGp in tmpPublicSet)
                    {
                        publicSet.Add(addGp);
                    }
                }
                level++;
            }
            bool deadEnd = false;
            if (!isGlobalGoal)
                deadEnd = true;
            HashSet<GroundedPredicate> publicGoals = new HashSet<GroundedPredicate>();
            foreach (MapsAgent agent in agents)
            {
                var items = agent.GetPublicfactsGoals();
                foreach (GroundedPredicate publicGoal in items)
                {
                    publicGoals.Add(publicGoal);
                }
                Program.ffMessageCounter++;
            }
            foreach (MapsAgent agent in agents)
            {
                agent.InitRelaxtionPlan();
                Program.ffMessageCounter++;
            }
            flag2 = true;
            while (flag2)
            {
                flag2 = false;
                HashSet<GroundedPredicate> newPublicGoals = new HashSet<GroundedPredicate>();
                string ans = "";
                foreach (MapsAgent agent in agents)
                {

                    string localAns;
                    var pGoals = agent.UpDateRelaxtionPlan(publicGoals, out localAns);
                    foreach (var gp in pGoals)
                        if (!newPublicGoals.Contains(gp))
                            newPublicGoals.Add(gp);
                    if (localAns.Equals("continue"))
                        flag2 = true;
                    Program.ffMessageCounter++;
                }
                if (publicGoals.Count > 0 && !deadEnd)
                    throw new Exception("bug"); ;
                publicGoals = newPublicGoals;
            }
            int count = 0;
            if (deadEnd)
                count = 1000;
            preferFacts = new HashSet<GroundedPredicate>();
            foreach (MapsAgent agent in agents)
            {
                count += agent.GetRelaxPlanSize();
                preferFacts.UnionWith(agent.GetRelaxPlanPreconditions());
                Program.ffMessageCounter++;
            }

            return count;
        }
        public void ApplyPublicEffects(Formula eff, HashSet<GroundedPredicate> publicFacts, HashSet<GroundedPredicate> allPublicFacts)
        {
            HashSet<Predicate> lAdd = new HashSet<Predicate>();
            HashSet<Predicate> lDelete = new HashSet<Predicate>();
            GetApplicableEffects(eff, lAdd, lDelete);
            foreach (GroundedPredicate p in lDelete)
            {
                if (allPublicFacts.Contains((GroundedPredicate)p.Negate()) || allPublicFacts.Contains((GroundedPredicate)p))
                {
                    publicFacts.Add(p);
                    publicFacts.Remove((GroundedPredicate)p.Negate());

                }
            }

            foreach (GroundedPredicate p in lAdd)
            {
                if (allPublicFacts.Contains((GroundedPredicate)p) || allPublicFacts.Contains((GroundedPredicate)p.Negate()))
                {
                    publicFacts.Add(p);
                    publicFacts.Remove((GroundedPredicate)p.Negate());
                }
            }
        }
        public void ApplyPublicEffects2(List<Predicate> eff, HashSet<GroundedPredicate> publicFacts, HashSet<GroundedPredicate> allPublicFacts)
        {
            HashSet<Predicate> lAdd = new HashSet<Predicate>();
            HashSet<Predicate> lDelete = new HashSet<Predicate>();

            foreach (GroundedPredicate p in eff)
            {
                if (allPublicFacts.Contains((GroundedPredicate)p.Negate()) || allPublicFacts.Contains((GroundedPredicate)p))
                {
                    publicFacts.Add(p);
                    publicFacts.Remove((GroundedPredicate)p.Negate());

                }
            }


        }
        public void GetApplicableEffects(Formula fEffects, HashSet<Predicate> lAdd, HashSet<Predicate> lDelete)
        {
            if (fEffects is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)fEffects).Predicate;
                if (p.Negation)
                    lDelete.Add(p);
                else
                    lAdd.Add(p);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)fEffects;

                if (cf.Operator == "and")
                {
                    foreach (Formula f in cf.Operands)
                    {
                        GetApplicableEffects(f, lAdd, lDelete);
                    }
                }
            }
        }
        public bool IsGoal(List<GroundedPredicate> lGoal)
        {
            HashSet<GroundedPredicate> completeState = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate pGp in publicFacts)
            {
                completeState.Add(pGp);
            }

            foreach (var ma in mapsAgents)
            {
                State pState = ma.Value.GetPrivateState(stateIndexes[ma.Key]);
                foreach (GroundedPredicate gp in pState.m_lPredicates)
                {
                    completeState.Add(gp);
                }
            }
            
                foreach (GroundedPredicate gp in agentsGoals)
                {
                    if (!completeState.Contains(gp))
                        return false;
                }
            
            return true;
        }
        public void ChangeAgent(string newAgent, List<Order> orderList, List<Landmark> publicRelevantLandmark, List<Order> ReasonableOrdering)
        {
            if (othersCourrentState != null)
            {
                othersCourrentState.Remove(agent);
                othersCourrentState.Remove(newAgent);
            }
            agent = newAgent;
            state = new State(mapsAgents[agent].GetPrivateState(stateIndexes[agent]));
            foreach (GroundedPredicate gp in publicFacts)
            {
                state.AddPredicate(gp);
            }
            lastPrivateIndex = stateIndexes[agent];

            if(Program.projectionVersion == Program.ProjectionVersion.ProjectionFF)
            {
               // GetProjection_h();
               //memH = h;
               //h = old_h;
            }
            // h = GetProjection_h();

        }

        public void updateH()
        {
            h = memH;
        }
        int memH = 0;
        public override bool Equals(object obj)
        {
            // return (GetHashCode() == ((State)obj).GetHashCode());
            if (obj is MapsVertex)
            {
                MapsVertex s = (MapsVertex)obj;

                if ((s.returnTo != null && returnTo != null) && !returnTo.Equals(s.returnTo))
                    return false;
                if (s.isPreferable)
                {
                    if(relaxPlan == null && s.relaxPlan != null) 
                        return false;
                    if(s.relaxPlan != null && relaxPlan != null && !relaxPlan.Equals(s.relaxPlan))
                        return false;
                }
                foreach (var kv in s.stateIndexes)
                {
                    if (!stateIndexes.ContainsKey(kv.Key) || !stateIndexes[kv.Key].Equals(kv.Value))
                        return false;
                }

                if (s.publicFacts.Count != publicFacts.Count)
                    return false;

                foreach (GroundedPredicate p in s.publicFacts)
                    if (!publicFacts.Contains(p))
                        return false;

                if (s.returnTo == null && returnTo != null)
                    return false;

                return true;

            }
            return false;
        }
        public override string ToString()
        {
            string str = "";
            foreach (var kv in stateIndexes)
            {
                str += kv.Key + ": " + kv.Value + " ,";
            }
            return str + " h=" + h;
        }
        public override int GetHashCode()
        {
            if (code != -1) return code;
            // if (returnTo != null)
            //   code += returnTo.GetHashCode();
            foreach (var kv in stateIndexes)
            {
                code += kv.Key.GetHashCode() + kv.Value.GetHashCode();
            }
            foreach (GroundedPredicate gp in publicFacts)
            {
                code += gp.GetHashCode();
            }
            return code;
        }
        private int SatisfyLandmark(int indexLandmarks, HashSet<Predicate> newState, bool[] landmarks, out bool[] notSatisfiedLandmarks, List<Order> orderList, List<Landmark> publicRelevantLandmark, bool[] reasonableOrderingVector, out bool[] outReasonableOrdering, List<Order> ReasonableOrdering)
        {

            outReasonableOrdering = new bool[reasonableOrderingVector.Length];
            Array.Copy(reasonableOrderingVector, outReasonableOrdering, reasonableOrderingVector.Length);
            int notSatisfied = 0;
            bool f = false;
            notSatisfiedLandmarks = new bool[landmarks.Length];
            if (indexLandmarks < landmarks.Length)
                Array.Copy(landmarks, indexLandmarks, notSatisfiedLandmarks, indexLandmarks, landmarks.Length - indexLandmarks);

            for (int i = 0; i < indexLandmarks; i++)
            {
                f = false;
                if (landmarks[i] == false)
                {
                    foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                    {
                        if (newState.Contains(fact))
                        {
                            notSatisfiedLandmarks[i] = true;
                            f = true;
                            for (int k = 0; k < outReasonableOrdering.Length; k++)
                            {
                                if (outReasonableOrdering[k] == false && ReasonableOrdering[k].lendmark1.Equals(publicRelevantLandmark[i]))
                                {
                                    outReasonableOrdering[k] = true;
                                }
                            }
                            break;
                        }

                    }

                    if (!f)
                    {
                        notSatisfiedLandmarks[i] = false;
                        notSatisfied += 1;// publicRelevantLandmark[i].worth;
                    }
                }
                else
                {
                    if (publicRelevantLandmark[i].facts.ElementAt(0).Value.Equals("Goal"))
                    {
                        foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                        {
                            if (newState.Contains(fact))
                            {
                                notSatisfiedLandmarks[i] = true;
                                f = true;
                                break;
                            }

                        }

                        if (!f)
                        {
                            notSatisfiedLandmarks[i] = false;
                            notSatisfied += 1;//publicRelevantLandmark[i].worth;
                        }

                    }
                    else
                    {
                        notSatisfiedLandmarks[i] = true;
                    }


                }
            }

            bool agein = true;
            while (agein)
            {
                agein = false;
                for (int i = 0; i < indexLandmarks; i++)
                {
                    f = false;
                    if (notSatisfiedLandmarks[i] == true)
                    {


                        foreach (Order order in orderList)
                        {
                            if (order.lendmark1.Equals(publicRelevantLandmark[i]))
                            {
                                int index = publicRelevantLandmark.IndexOf(order.lendmark2);
                                if (index > 0)
                                {
                                    if (notSatisfiedLandmarks[index] == false)
                                    {
                                        foreach (GroundedPredicate fact in publicRelevantLandmark[i].facts.Keys)
                                        {
                                            if (newState.Contains(fact))
                                            {
                                                notSatisfiedLandmarks[i] = true;
                                                f = true;
                                                break;
                                            }

                                        }

                                        if (!f)
                                        {
                                            notSatisfiedLandmarks[i] = false;
                                            notSatisfied += 1;//publicRelevantLandmark[i].worth;
                                            agein = true;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        int counter = 0;
                        foreach (Order order in ReasonableOrdering)
                        {
                            if (outReasonableOrdering[counter] == false)
                            {
                                if (order.lendmark2.Equals(publicRelevantLandmark[i]))
                                {
                                    int index = publicRelevantLandmark.IndexOf(order.lendmark1);
                                    if (notSatisfiedLandmarks[index] == false)
                                    {
                                        notSatisfiedLandmarks[i] = false;
                                        notSatisfied += 1;//publicRelevantLandmark[i].worth;
                                        agein = true;
                                        break;
                                    }
                                }
                            }
                            counter++;
                        }

                    }

                }
            }
            return notSatisfied;
        }


        public static int ComparerByLandmark(MapsVertex v1, MapsVertex v2)
        {
            if (v1.h == v2.h)
            {
                //if (v1.publicCount < v2.publicCount)
                //   return 1;
                //if (v1.publicCount > v2.publicCount)
                //    return -1;
                if (v1.g == v2.g)
                    return 0;
                if (v1.g > v2.g)
                    return 1;
                else
                    return -1;



            }
            if (v1.h > v2.h) return 1;
            return -1;

        }
        public static int ComparerByFF(MapsVertex v1, MapsVertex v2)
        {
            if (v1.h2 == v2.h2)
            {
                //if (v1.publicCount < v2.publicCount)
                //   return 1;
                //if (v1.publicCount > v2.publicCount)
                //    return -1;
                if (v1.g == v2.g)
                    return 0;
                if (v1.g > v2.g)
                    return 1;
                else
                    return -1;



            }
            if (v1.h2 > v2.h2) return 1;
            return -1;

        }
        public HashSet<GroundedPredicate> GetFullState()
        {
            HashSet<GroundedPredicate> completeState = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate pGp in publicFacts)
            {
                if (!pGp.Negation)
                    completeState.Add(pGp);
            }

            foreach (var ma in mapsAgents)
            {
                State pState = ma.Value.GetPrivateState(stateIndexes[ma.Key]);
                foreach (GroundedPredicate gp in pState.m_lPredicates)
                {
                    if (!gp.Negation)
                        completeState.Add(gp);
                }
            }
            return completeState;
        }
        public static int Comparer2(MapsVertex v1, MapsVertex v2)
        {
            if (v1.h + v1.g == v2.h + v2.g)
            {
                //if (v1.publicCount < v2.publicCount)
                //   return 1;
                //if (v1.publicCount > v2.publicCount)
                //    return -1;
                if (v1.g == v2.g)
                    return 0;
                if (v1.g > v2.g)
                    return -1;
                else
                    return 1;



            }
            if (v1.h + v1.g > v2.h + v2.g) return 1;
            return -1;

        }
    }
}
