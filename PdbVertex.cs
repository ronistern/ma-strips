using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;

namespace Planning
{
    class PdbVertex
    {
        public List<string> History = new List<string>();
        public static List<Agent> agents = null;
        public HashSet<CompoundFormula> canGetInParallel;
        public List<HashSet<CompoundFormula>> publicPredicateImplications = null;
        public static Dictionary<string, int> map = null;
        public static Domain d;
        public static Problem p;
        public PdbVertex Parent { get; private set; }
        public static HSPHeuristic hsp = null;
        public static ForwardSearchPlanner forwardSearch = null;
        public List<Action> lplan = null;
        public List<HashSet<CompoundFormula>> Potential = null;
        public State publicState = null;
        public static List<string> ffLplan = null;
        // private List<Landmark> restLandmark = null;
        public int[] statesNubmber;
        public double g = 0;
        public double h = 0;
        public double cost = 0;
        public static List<Landmark> goals;
        public static PatternDatabase pd = null;
        public Dictionary<Landmark, int> disFromGoals = null;
        HashSet<Predicate> JointPublicPredicates = new HashSet<Predicate>();

        public int ID { get; private set; }
        public static int VERTEX_COUNT = 0;

        
        public static void initVertxClass(List<Agent> m_agents)
        {
            agents = m_agents;

            map = new Dictionary<string, int>();
            for (int i = 0; i < agents.Count; i++)
            {
                map.Add(agents[i].name, i);

            }

        }
        public static void initVertxClass(List<Agent> m_agents, Domain m_d, Problem m_p, List<Landmark> goalsList, PatternDatabase pD)
        {
            d = m_d;
            p = m_p;
            agents = m_agents;
            map = new Dictionary<string, int>();
            for (int i = 0; i < agents.Count; i++)
            {
                map.Add(agents[i].name, i);
            }
            goals = goalsList;
            pd = pD;
        }

        public void initVertx(Dictionary<Landmark, int> ParentDisFromGoals)
        {


            disFromGoals = new Dictionary<Landmark, int>();



            for (int i = 0; i < agents.Count; i++)
            {
                h += agents[i].CantReachTheGoal(statesNubmber[i]);

            }

            foreach (Landmark g in goals)
            {
                if (ParentDisFromGoals != null && !g.facts.ElementAt(0).Value.Equals("goal") && ParentDisFromGoals[g] == 0)
                {
                    disFromGoals.Add(g, 0);
                    continue;
                }
                else
                    disFromGoals.Add(g, 1000);


                foreach (Agent agent in agents)
                {
                    int cost = agent.h(pd, g, statesNubmber[map[agent.name]]);
                    if (cost < disFromGoals[g])
                    {
                        disFromGoals[g] = cost;
                        //continue;
                    }
                }

            }

            foreach (int cost in disFromGoals.Values)
            {
                h += cost;
              

            }

        }

        public PdbVertex(int[] m_statesNubmber, List<Action> m_lplan, double new_G, double m_h, double m_cost, List<HashSet<CompoundFormula>> pot, Dictionary<Landmark, int> ParentDisFromGoals)
        {
            ID = VERTEX_COUNT++;

            
            statesNubmber = m_statesNubmber;
            foreach (int Vnum in statesNubmber)
            {
                if (Vnum == -1)
                {
                    h = -1;
                    return;
                }
            }
            cost = m_cost;
            g = new_G;
            HashSet<GroundedPredicate> publicPredicate = new HashSet<GroundedPredicate>();
            h = m_h;

            lplan = new List<Action>(m_lplan);
            initVertx(ParentDisFromGoals);
        }




        public PdbVertex Apply(string agentName, Action act)
        {
            if (!agents[map[agentName]].CanDo(statesNubmber[map[agentName]], act))
                return null;

            int[] newStateNumbers = new int[agents.Count];
            double m_h = 0;
            KeyValuePair<int, double> ans;
            CompoundFormula eff;
            if (act.Effects is CompoundFormula)
            {
                eff = (CompoundFormula)act.Effects;
            }
            else
            {
                eff = new CompoundFormula("and");
                eff.AddOperand(act.Effects);
            }
            for (int i = 0; i < agents.Count; i++)
            {
                ans = agents[i].PdbDemoApply(statesNubmber[i], agentName, eff, act.HashPrecondition,act);

                newStateNumbers[i] = ans.Key;

            }

            PdbVertex newVertex = new PdbVertex(newStateNumbers, lplan, g + 1, m_h, cost, Potential, disFromGoals);
            if (newVertex.h == -1)
                return null;
            newVertex.Parent = this;
            newVertex.lplan.Add(act);
            newVertex.publicState = publicState.ApplyEffect(act, agents[map[agentName]].PublicPredicates);
            newVertex.JointPublicPredicates = new HashSet<Predicate>();
            foreach (Predicate p in newVertex.publicState.Predicates)
                if (!p.Negation)
                    newVertex.JointPublicPredicates.Add(p);
            
            return newVertex;
        }

        public string IsGoal(out List<string> finalPlan)
        {

            finalPlan = null;
            //if (h > 0) return "false";
            for (int i = 0; i < agents.Count; i++)
            {
                if (!agents[i].ReachTheGoal(statesNubmber[i]))
                    return "false";
            }

            string fault;


            if (this.hspPlaner(out finalPlan, out fault))
                return "true";
            if (this.GroundingActions(out finalPlan, out fault))
                return "true";
            if (this.RegGrounding(out finalPlan, out fault))
                return "true";
            
            if(this.GetGroundPlan(out fault, out finalPlan))
                return "true";
            
            fault = "false";
            return fault;


        }
        bool threadContinueSearchFlag = true;
        public List<bool> threadAns = null;
        public bool GetGroundPlan(out string f, out List<string> finalPlan)
        {
            //Console.WriteLine("\nPublic global plan found, searching for private plans");
            finalPlan = new List<string>();
            threadContinueSearchFlag = true;
            Dictionary<string, State> agentState = new Dictionary<string, State>();
            List<List<Action>> groupingAction = new List<List<Action>>();
            Dictionary<int, List<string>> dicFinalPlan = new Dictionary<int, List<string>>();
            foreach (Action act in this.lplan)
            {

                List<Action> tmp = new List<Action>();
                tmp.Add(act);
                groupingAction.Add(tmp);
            }
            Group(groupingAction);
            try
            {
                List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
                Dictionary<string, CompoundFormula> agentFormula = null;
                foreach (List<Action> actions in groupingAction)
                {
                    agentFormula = new Dictionary<string, CompoundFormula>();
                    bool flag = false;
                    foreach (Action act in actions)
                    {
                        if (!agentFormula.ContainsKey(act.agent))
                            agentFormula.Add(act.agent, new CompoundFormula("and"));

                        foreach (GroundedPredicate gp in act.HashEffects)
                        {
                            if (!gp.Negation && agents[map[act.agent]].PublicPredicates.Contains(gp))
                            {
                                //if (allKindOfpublicPreconditions.Contains(gp))
                                {
                                    agentFormula[act.agent].AddOperand(gp);
                                    flag = true;
                                }

                            }
                        }
                    }
                    foreach (var agFormula in agentFormula)
                        lplan.Add(new KeyValuePair<string, CompoundFormula>(agFormula.Key, agFormula.Value));
                }
                foreach (Agent a in agents)
                {
                    agentState.Add(a.name, new State(a.startState));
                }
                threadAns = new List<bool>();
                List<Thread> threads = new List<Thread>();
                for (int i = 0; i < agents.Count; i++)
                {
                    State s = agentState[agents[i].name];
                    Agent agent = agents[i];
                    string name = agents[i].name;
                    Thread agentPlanning = new Thread(() => AgentsGrounding(agent, dicFinalPlan, name, s, lplan));
                    agentPlanning.Start();
                    threads.Add(agentPlanning);
                    //agentPlanning.Join();
                }
                foreach (Thread t in threads)
                {
                    t.Join(5 * 60000);
                }

                if (threadAns.Count != agents.Count)
                {
                    threadContinueSearchFlag = false;
                    foreach (Thread t in threads)
                    {
                        t.Join();
                    }
                    finalPlan = null;
                    return RegGrounding(out finalPlan, out f);

                }
                for (int i = 0; i < dicFinalPlan.Count; i++)
                {
                    finalPlan.AddRange(dicFinalPlan[i]);
                }
                Dictionary<string, CompoundFormula> agentGoal = new Dictionary<string, CompoundFormula>();

                foreach (Agent a in agents)
                {
                    agentGoal.Add(a.name, new CompoundFormula("and"));
                    foreach (GroundedPredicate goalPredicate in a.goal)
                    {
                        agentGoal[a.name].AddOperand(goalPredicate);
                    }

                }
                foreach (var agent in agents)
                {
                    if (agentGoal[agent.name].Operands.Count > 0)
                    {

                        bool bUnsolvable = false;
                        ExternalPlanners externalPlanners = new ExternalPlanners();
                        // ffLplan = externalPlanners.Plan(true, true, agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);

                        ffLplan = externalPlanners.FFPlan(agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);
                        if (ffLplan != null)
                        {

                            List<string> todo = ffLplan;

                            foreach (string act in todo)
                            {
                                agentState[agent.name] = agentState[agent.name].ApplyII(agents[map[agent.name]].domain.mapActionNameToAction[act]);
                                finalPlan.Add(act);
                                foreach (Agent a in agents)
                                {
                                    if (!a.name.Equals(agent.name))
                                    {

                                        agentState[a.name] = agentState[a.name].ApplyEffect(agents[map[agent.name]].domain.mapActionNameToAction[act], a.Predicates);
                                    }
                                }
                            }
                        }
                        else
                        {
                            finalPlan = null;
                            return RegGrounding(out finalPlan, out f);


                        }
                    }
                }
                foreach (var agSt in agentState)
                {
                    if (agSt.Value == null)
                    {
                        finalPlan = null;
                        return RegGrounding(out finalPlan, out f);

                    }
                }

                /* State sCurrent = new State(globalInitialState);
                 foreach (string sAction in finalPlan)
                 {
                     State sNew = sCurrent.Apply(sAction, joinDomain);
                     if (sNew == null)
                     {
                         string f;
                         List<string> path = null;
                         RegGrounding(out path, out f);
                         return path;
                     }
                     sCurrent = sNew;
                 }*/
                f = "true";
                return true;
            }
            catch (Exception ex)
            {
                finalPlan = null;
                return RegGrounding(out finalPlan, out f);
            }
        }
        public void Group(List<List<Action>> groupingActions)
        {
            for (int i = 1; i < groupingActions.Count; i++)
            {
                for (int j = 0; j < groupingActions[i].Count; j++)
                {
                    Action courentAction = groupingActions[i][j];
                    int nextIndex = i;
                    for (int k = i - 1; k > -1; k--)
                    {
                        bool canPass = true;
                        foreach (Action beforeMeAction in groupingActions[k])
                        {
                            foreach (GroundedPredicate pre in courentAction.HashPrecondition)
                            {
                                if (beforeMeAction.HashEffects.Contains(pre))
                                {
                                    canPass = false;
                                    break;
                                }
                            }
                            if (!canPass)
                                break;
                            foreach (GroundedPredicate pre in courentAction.HashEffects)
                            {
                                if (beforeMeAction.HashPrecondition.Contains(pre.Negate()))
                                {
                                    canPass = false;
                                    break;
                                }
                            }
                            if (!canPass)
                                break;

                        }
                        if (!canPass)
                            break;
                        nextIndex = k;
                    }
                    if (nextIndex < i)
                    {
                        groupingActions[i].RemoveAt(j);
                        j--;
                        groupingActions[nextIndex].Add(courentAction);
                    }
                }
            }
        }
        public static Mutex mutex = new Mutex();
        public static Mutex mutex2 = new Mutex();
        public void AgentsGrounding(Agent agent, Dictionary<int, List<string>> finalPlan, string m_agentName, State agentState, List<KeyValuePair<string, CompoundFormula>> m_lplan)
        {
            List<string> ffLplan = null;
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            mutex2.WaitOne();
            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>(m_lplan);
            // Dictionary<string, int> map = new Dictionary<string, int>(AdvancedLandmarkProjectionPlaner.map);
            mutex2.ReleaseMutex();
            CompoundFormula goalFormula = new CompoundFormula("and");
            string agentName;
            int counter = 0;
            foreach (KeyValuePair<string, CompoundFormula> eff in lplan)
            {
                agentName = eff.Key;
                goalFormula = new CompoundFormula(eff.Value);
                if (agentName.Equals(m_agentName))
                {
                    if (!threadContinueSearchFlag)
                        return;

                    mutex.WaitOne();
                    finalPlan.Add(counter, new List<string>());
                    mutex.ReleaseMutex();
                    bool bUnsolvable = false;
                    ExternalPlanners externalPlanners = new ExternalPlanners();
                    ffLplan = externalPlanners.FFPlan(agent.domain, agent.problem, agentState, goalFormula, agent.m_actions, 5 * 60 * 1000, out bUnsolvable);
                    if (ffLplan != null)
                    {
                        List<string> todo = ffLplan;
                        foreach (string act in todo)
                        {
                            bool flag = agentState.FullApplyII(agent.domain.mapActionNameToAction[act]);
                            if (!flag || !threadContinueSearchFlag)
                                return;
                            mutex.WaitOne();
                            finalPlan[counter].Add(act);
                            mutex.ReleaseMutex();
                        }

                    }
                    else
                    {
                        return;
                    }

                }
                else
                {
                    agentState.FullApplyFormulaEffect(goalFormula);
                }
                counter++;
            }
            mutex.WaitOne();
            threadAns.Add(true);
            mutex.ReleaseMutex();
        }
        bool isPrivateGoal = true;

        public bool RegGrounding(out List<string> finalPlan, out string fault)
        {
            Console.WriteLine("\nPublic global plan found, searching for private plans");
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<List<Action>> groupingAction = new List<List<Action>>();
            Dictionary<int, List<string>> dicFinalPlan = new Dictionary<int, List<string>>();
            foreach (Action act in this.lplan)
            {
                List<Action> tmp = new List<Action>();
                tmp.Add(act);
                groupingAction.Add(tmp);
            }
            Group(groupingAction);

            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
            Dictionary<string, CompoundFormula> agentFormula = null;
            foreach (List<Action> actions in groupingAction)
            {
                agentFormula = new Dictionary<string, CompoundFormula>();
                bool flag = false;
                foreach (Action act in actions)
                {
                    if (!agentFormula.ContainsKey(act.agent))
                        agentFormula.Add(act.agent, new CompoundFormula("and"));

                    foreach (GroundedPredicate gp in act.HashEffects)
                    {
                        if (agents[map[act.agent]].PublicPredicates.Contains(gp))
                        {
                            //if (allKindOfpublicPreconditions.Contains(gp))
                           // if(!gp.Negation)
                            {
                                agentFormula[act.agent].AddOperand(gp);
                                flag = true;
                            }

                        }
                    }
                }
                foreach (var agFormula in agentFormula)
                {
                    if(agFormula.Value.Operands.Count>0)
                        lplan.Add(new KeyValuePair<string, CompoundFormula>(agFormula.Key, agFormula.Value));
                }
            }

            /* foreach (Action act in this.lplan)
             {
                 CompoundFormula effect = new CompoundFormula("and");
                 bool flag = false;
                 foreach (GroundedPredicate gp in act.HashEffects)
                 {
                     if (agents[map[act.agent]].PublicPredicates.Contains(gp))
                     {
                         effect.AddOperand(gp);
                         flag = true;
                     }
                 }
                 if (flag)
                     lplan.Add(new KeyValuePair<string, CompoundFormula>(act.agent, effect));
             }*/
            int count = 0;
            finalPlan = new List<string>();
            fault = "";
            int level = 0;

            Dictionary<string, State> agentState = new Dictionary<string, State>();
            foreach (Agent a in agents)
            {
                agentState.Add(a.name, new State(a.startState));
            }
            CompoundFormula goalFormula = new CompoundFormula("and");
            string agentName;
            foreach (KeyValuePair<string, CompoundFormula> eff in lplan)
            {
                agentName = eff.Key;
                goalFormula = new CompoundFormula(eff.Value);

               /*  HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
                 foreach (GroundedPredicate gp in goalFormula.GetAllPredicates())
                 {
                     if (agents[map[agentName]].MutuallyExclusive.ContainsKey(gp))
                     {
                         foreach (GroundedPredicate mgp in agents[map[agentName]].MutuallyExclusive[gp])
                             mutex.Add(mgp);
                     }
                 }
                
                 foreach (GroundedPredicate publicPos in agents[map[agentName]].PublicPredicates)
                 {
                     if (agentState[agentName].m_lPredicates.Contains(publicPos))
                     {
                         if (!publicPos .Negation && !mutex.Contains(publicPos) && !goalFormula.GetAllPredicates().Contains(publicPos.Negate()))
                             goalFormula.AddOperand(publicPos);
                     }
                 }*/
                  
                bool bUnsolvable = false;
                ExternalPlanners externalPlanners = new ExternalPlanners();
                ffLplan = externalPlanners.FFPlan(agents[map[agentName]].domain, agents[map[agentName]].problem, agentState[agentName], goalFormula, agents[map[agentName]].m_actions, 5 * 60 * 1000, out bUnsolvable);

                //List<string> todo = Plan(d, p, agentState[agentName], goalFormula, agents[map[agentName]].m_actions);
                //planTheard = new Thread(() => FF_Plan(agents[map[agentName]].domain, agents[map[agentName]].problem, agentState[agentName], goalFormula, agents[map[agentName]].m_actions));
                //List<string> todo = Plan(d, p, agentState[agentName], localGoal, agents[map[agentName]].m_actions);
                //planTheard.Start();
                //planTheard.Join(3000);
                //planTheard.Abort();
                if (ffLplan != null)
                {
                    List<string> todo = ffLplan;
                    foreach (string act in todo)
                    {
                        State s = agentState[agentName].ApplyII(agents[map[agentName]].domain.mapActionNameToAction[act]);
                        if (s == null)
                            throw new Exception();
                        agentState[agentName] = s;
                        finalPlan.Add(act);
                        foreach (Agent a in agents)
                        {
                            if (!a.name.Equals(agentName))
                            {

                                agentState[a.name] = agentState[a.name].ApplyEffect(agents[map[agentName]].domain.mapActionNameToAction[act], a.Predicates);
                            }
                        }
                    }

                }
                else
                {
                    Program.KillPlanners();
                    return GroundingActions(out finalPlan, out fault);
                }


            }
            Dictionary<string, CompoundFormula> agentGoal = new Dictionary<string, CompoundFormula>();
            Dictionary<string, bool> agentFlag = new Dictionary<string, bool>();
            foreach (Agent a in agents)
            {
                agentFlag.Add(a.name, false);
                agentGoal.Add(a.name, new CompoundFormula("and"));
                foreach (GroundedPredicate goalPredicate in a.goal)
                {
                    if (!a.PublicPredicates.Contains(goalPredicate))
                        agentFlag[a.name] = true;
                    bool sat = false;
                    /* foreach (var state in agentState.Values)
                     {
                         if (state.m_lPredicates.Contains(goalPredicate))
                         {
                             sat = true;
                             break;
                         }
                     }*/
                    if (true)//!sat)
                    {
                        agentGoal[a.name].AddOperand(goalPredicate);
                    }

                }
                /*  HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
                  foreach (GroundedPredicate gp in agentGoal[a.name].GetAllPredicates())
                  {
                      if (a.MutuallyExclusive.ContainsKey(gp))
                      {
                          foreach (GroundedPredicate mgp in a.MutuallyExclusive[gp])
                              mutex.Add(mgp);
                      }
                  }
                  foreach (GroundedPredicate publicPos in a.PublicPredicates)
                  {
                      if (agentState[a.name].m_lPredicates.Contains(publicPos) && !mutex.Contains(publicPos))
                          agentGoal[a.name].AddOperand(publicPos);
                  }*/
            }
            if (isPrivateGoal)
            {
                foreach (var agent in agents)
                {
                    if (agentGoal[agent.name].Operands.Count > 0 && agentFlag[agent.name])
                    {
                        //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name]);
                        // hsp = new HSPHeuristic(agent.m_actions, agentGoal[agent.name].GetAllPredicates().ToList(), admisabiliy);
                        //  forwardSearch = new ForwardSearchPlanner(agent.m_actions, hsp);
                        // List<Action> todo = forwardSearch.Plan(agentState[agent.name], agentGoal[agent.name].GetAllPredicates().ToList());
                        //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name], agent.m_actions);
                        bool bUnsolvable = false;
                        ExternalPlanners externalPlanners = new ExternalPlanners();
                        ffLplan = externalPlanners.FFPlan(agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);

                        //ffLplan = externalPlanners.FFPlan(agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);
                        if (ffLplan != null)
                        {

                            List<string> todo = ffLplan;

                            foreach (string act in todo)
                            {
                                agentState[agent.name] = agentState[agent.name].ApplyII(agents[map[agent.name]].domain.mapActionNameToAction[act]);
                                finalPlan.Add(act);
                                foreach (Agent a in agents)
                                {
                                    if (!a.name.Equals(agent.name))
                                    {

                                        agentState[a.name] = agentState[a.name].ApplyEffect(agents[map[agent.name]].domain.mapActionNameToAction[act], a.Predicates);
                                    }
                                }
                            }
                        }
                        else
                        {
                            Program.KillPlanners();
                            return GroundingActions(out finalPlan, out fault);

                        }
                    }
                }
            }
            foreach (var agSt in agentState)
            {
                if (agSt.Value == null)
                {
                    Program.KillPlanners();
                    return GroundingActions(out finalPlan, out fault);
                }
            }

            return true;


        }
        private bool hspPlaner(out List<string> finalPlan, out string fault)
        {
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<List<Action>> groupingAction = new List<List<Action>>();
            Dictionary<int, List<string>> dicFinalPlan = new Dictionary<int, List<string>>();
            foreach (Action act in this.lplan)
            {
                List<Action> tmp = new List<Action>();
                tmp.Add(act);
                groupingAction.Add(tmp);
            }
            Group(groupingAction);

            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
            Dictionary<string, CompoundFormula> agentFormula = null;
            foreach (List<Action> actions in groupingAction)
            {
                agentFormula = new Dictionary<string, CompoundFormula>();
                bool flag = false;
                foreach (Action act in actions)
                {
                    if (!agentFormula.ContainsKey(act.agent))
                        agentFormula.Add(act.agent, new CompoundFormula("and"));

                    foreach (GroundedPredicate gp in act.HashEffects)
                    {
                        if (agents[map[act.agent]].PublicPredicates.Contains(gp))
                        {
                            //if (allKindOfpublicPreconditions.Contains(gp))
                            // if(!gp.Negation)
                            {
                                agentFormula[act.agent].AddOperand(gp);
                                flag = true;
                            }

                        }
                    }
                }
                foreach (var agFormula in agentFormula)
                {
                    if (agFormula.Value.Operands.Count > 0)
                        lplan.Add(new KeyValuePair<string, CompoundFormula>(agFormula.Key, agFormula.Value));
                }
            }
            /*foreach (Action act in this.lplan)
            {
                CompoundFormula effect = new CompoundFormula("and");
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (agents[map[act.agent]].PublicPredicates.Contains(gp))
                        effect.AddOperand(gp);
                }
                lplan.Add(new KeyValuePair<string, CompoundFormula>(act.agent, effect));
            }
            int count = 0;*/
            // foreach()
            {

            }

            finalPlan = new List<string>();
            fault = "";
            int level = 0;
            try
            {

                //return true;
                bool admisabiliy = false;
                Dictionary<string, State> agentState = new Dictionary<string, State>();
                foreach (Agent a in agents)
                {
                    agentState.Add(a.name, new State(a.startState));
                }
                CompoundFormula goalFormula = new CompoundFormula("and");
                string agentName = "";
                foreach (KeyValuePair<string, CompoundFormula> eff in lplan)
                {
                    level++;
                    // if (!Contains(agentState[eff.Key], publicAction.HashPrecondition))
                    {
                        //List<string> todo = Plan(d, p, agentState[publicAction.agent], publicAction.Preconditions);
                        List<Predicate> localGoal = new List<Predicate>();
                        foreach (GroundedPredicate p in eff.Value.GetAllPredicates())
                        {
                            if (agents[map[eff.Key]].PublicPredicates.Contains(p))
                                localGoal.Add(p);
                        }
                        /*HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
                        foreach (GroundedPredicate gp in localGoal)
                        {
                            if (agents[0].MutuallyExclusive.ContainsKey(gp))
                            {
                                foreach (GroundedPredicate mgp in agents[0].MutuallyExclusive[gp])
                                    mutex.Add(mgp);
                            }
                        }
                        foreach (GroundedPredicate publicPos in agents[map[eff.Key]].PublicPredicates)
                        {
                            if (agentState[eff.Key].m_lPredicates.Contains(publicPos))
                            {
                                if (!mutex.Contains(publicPos) && !localGoal.Contains(publicPos.Negate()))
                                    localGoal.Add(publicPos);
                            }
                        }*/

                        hsp = new HSPHeuristic(agents[map[eff.Key]].m_actions, localGoal, admisabiliy);
                        forwardSearch = new ForwardSearchPlanner(agents[map[eff.Key]].m_actions, hsp);
                        List<Action> todo = forwardSearch.Plan(agentState[eff.Key], localGoal);
                        foreach (Action act in todo)
                        {
                            agentState[eff.Key] = agentState[eff.Key].ApplyII(act);
                            finalPlan.Add(act.Name);
                            foreach (Agent a in agents)
                            {
                                if (!a.name.Equals(eff.Key))
                                {

                                    agentState[a.name] = agentState[a.name].ApplyEffect(act, a.Predicates);
                                }
                            }
                        }
                    }

                }
                Dictionary<string, CompoundFormula> agentGoal = new Dictionary<string, CompoundFormula>();
                Dictionary<string, bool> agentFlag = new Dictionary<string, bool>();
                foreach (Agent a in agents)
                {
                    agentFlag.Add(a.name, false);
                    agentGoal.Add(a.name, new CompoundFormula("and"));
                    foreach (GroundedPredicate goalPredicate in a.goal)
                    {
                        if (!a.PublicPredicates.Contains(goalPredicate))
                            agentFlag[a.name] = true;
                        bool sat = false;
                        /* foreach (var state in agentState.Values)
                         {
                             if (state.m_lPredicates.Contains(goalPredicate))
                             {
                                 sat = true;
                                 break;
                             }
                         }*/
                        if (true)//!sat)
                        {
                            agentGoal[a.name].AddOperand(goalPredicate);
                        }

                    }
                    /*  HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
                      foreach (GroundedPredicate gp in agentGoal[a.name].GetAllPredicates())
                      {
                          if (a.MutuallyExclusive.ContainsKey(gp))
                          {
                              foreach (GroundedPredicate mgp in a.MutuallyExclusive[gp])
                                  mutex.Add(mgp);
                          }
                      }
                      foreach (GroundedPredicate publicPos in a.PublicPredicates)
                      {
                          if (agentState[a.name].m_lPredicates.Contains(publicPos) && !mutex.Contains(publicPos))
                              agentGoal[a.name].AddOperand(publicPos);
                      }*/
                }
                if (isPrivateGoal)
                {
                    foreach (var agent in agents)
                    {
                        if (agentGoal[agent.name].Operands.Count > 0 && agentFlag[agent.name])
                        {
                            //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name]);
                            // hsp = new HSPHeuristic(agent.m_actions, agentGoal[agent.name].GetAllPredicates().ToList(), admisabiliy);
                            //  forwardSearch = new ForwardSearchPlanner(agent.m_actions, hsp);
                            // List<Action> todo = forwardSearch.Plan(agentState[agent.name], agentGoal[agent.name].GetAllPredicates().ToList());
                            //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name], agent.m_actions);
                            bool bUnsolvable = false;
                            ExternalPlanners externalPlanners = new ExternalPlanners();
                            ffLplan = externalPlanners.FFPlan(agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);

                            //ffLplan = externalPlanners.FFPlan(agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);
                            if (ffLplan != null)
                            {

                                List<string> todo = ffLplan;

                                foreach (string act in todo)
                                {
                                    agentState[agent.name] = agentState[agent.name].ApplyII(agents[map[agent.name]].domain.mapActionNameToAction[act]);
                                    finalPlan.Add(act);
                                    foreach (Agent a in agents)
                                    {
                                        if (!a.name.Equals(agent.name))
                                        {

                                            agentState[a.name] = agentState[a.name].ApplyEffect(agents[map[agent.name]].domain.mapActionNameToAction[act], a.Predicates);
                                        }
                                    }
                                }
                            }
                            else
                            {
                                Program.KillPlanners();
                                return GroundingActions(out finalPlan, out fault);

                            }
                        }
                    }
                }
                foreach (var agSt in agentState)
                {
                    if (agSt.Value == null) return false;
                }

                return true;
            }
            catch (Exception ex)
            {
                fault = level.ToString();
                return false;
            }
        }
        public bool GroundingActions(out List<string> finalPlan, out string fault)
        {
            Console.WriteLine("\nPublic global plan found, searching for private plans");
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<Action> lplan = new List<Action>();
            foreach (Action act in this.lplan)
            {
                lplan.Add(act);
            }
            int count = 0;
            finalPlan = new List<string>();
            fault = "";
            int level = 0;

            Dictionary<string, State> agentState = new Dictionary<string, State>();
            foreach (Agent a in agents)
            {
                agentState.Add(a.name, new State(a.startState));
            }
            CompoundFormula goalFormula = new CompoundFormula("and");
            string agentName;
            foreach (Action act in lplan)
            {
                agentName = act.agent;
                goalFormula = new CompoundFormula("and");
                foreach (GroundedPredicate gp in act.Preconditions.GetAllPredicates())
                {
                    goalFormula.AddOperand(gp);
                }
                //goalFormula = new CompoundFormula((CompoundFormula)act.Preconditions);

                bool bUnsolvable = false;
                ExternalPlanners externalPlanners = new ExternalPlanners();
                ffLplan = externalPlanners.FFPlan(agents[map[agentName]].domain, agents[map[agentName]].problem, agentState[agentName], goalFormula, agents[map[agentName]].privateActions, 5 * 60 * 1000, out bUnsolvable);

                //List<string> todo = Plan(d, p, agentState[agentName], goalFormula, agents[map[agentName]].m_actions);
                //planTheard = new Thread(() => FF_Plan(agents[map[agentName]].domain, agents[map[agentName]].problem, agentState[agentName], goalFormula, agents[map[agentName]].m_actions));
                //List<string> todo = Plan(d, p, agentState[agentName], localGoal, agents[map[agentName]].m_actions);
                //planTheard.Start();
                //planTheard.Join(3000);
                //planTheard.Abort();
                if (ffLplan != null)
                {
                    List<string> todo = ffLplan;
                    foreach (string localAct in todo)
                    {
                        State s = agentState[agentName].ApplyII(agents[map[agentName]].domain.mapActionNameToAction[localAct]);
                        if (s == null)
                            throw new Exception();
                        agentState[agentName] = s;
                        finalPlan.Add(localAct);
                        foreach (Agent a in agents)
                        {
                            if (!a.name.Equals(agentName))
                            {
                                agentState[a.name] = agentState[a.name].ApplyEffect(agents[map[agentName]].domain.mapActionNameToAction[localAct], a.Predicates);
                            }
                        }
                    }
                    State state = agentState[agentName].ApplyII(agents[map[agentName]].domain.mapActionNameToAction[act.Name]);
                    if (state == null)
                    {
                        return false;
                    }
                    agentState[agentName] = state;
                    finalPlan.Add(act.Name);
                    foreach (Agent a in agents)
                    {
                        if (!a.name.Equals(agentName))
                        {

                            agentState[a.name] = agentState[a.name].ApplyEffect(agents[map[agentName]].domain.mapActionNameToAction[act.Name], a.Predicates);
                        }
                    }
                }
                else
                {
                    Program.KillPlanners();
                    return false;
                }


            }
            Dictionary<string, CompoundFormula> agentGoal = new Dictionary<string, CompoundFormula>();
            Dictionary<string, bool> agentFlag = new Dictionary<string, bool>();
            foreach (Agent a in agents)
            {
                agentFlag.Add(a.name, false);
                agentGoal.Add(a.name, new CompoundFormula("and"));
                foreach (GroundedPredicate goalPredicate in a.goal)
                {
                    if (!a.PublicPredicates.Contains(goalPredicate))
                        agentFlag[a.name] = true;
                    bool sat = false;
                    /* foreach (var state in agentState.Values)
                     {
                         if (state.m_lPredicates.Contains(goalPredicate))
                         {
                             sat = true;
                             break;
                         }
                     }*/
                    if (true)//!sat)
                    {
                        agentGoal[a.name].AddOperand(goalPredicate);
                    }

                }
                /*  HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
                  foreach (GroundedPredicate gp in agentGoal[a.name].GetAllPredicates())
                  {
                      if (a.MutuallyExclusive.ContainsKey(gp))
                      {
                          foreach (GroundedPredicate mgp in a.MutuallyExclusive[gp])
                              mutex.Add(mgp);
                      }
                  }
                  foreach (GroundedPredicate publicPos in a.PublicPredicates)
                  {
                      if (agentState[a.name].m_lPredicates.Contains(publicPos) && !mutex.Contains(publicPos))
                          agentGoal[a.name].AddOperand(publicPos);
                  }*/
            }
            if (isPrivateGoal)
            {
                foreach (var agent in agents)
                {
                    if (agentGoal[agent.name].Operands.Count > 0 && agentFlag[agent.name])
                    {
                        //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name]);
                        // hsp = new HSPHeuristic(agent.m_actions, agentGoal[agent.name].GetAllPredicates().ToList(), admisabiliy);
                        //  forwardSearch = new ForwardSearchPlanner(agent.m_actions, hsp);
                        // List<Action> todo = forwardSearch.Plan(agentState[agent.name], agentGoal[agent.name].GetAllPredicates().ToList());
                        //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name], agent.m_actions);
                        bool bUnsolvable = false;
                        ExternalPlanners externalPlanners = new ExternalPlanners();
                        ffLplan = externalPlanners.FFPlan(agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);

                        //ffLplan = externalPlanners.FFPlan(agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);
                        if (ffLplan != null)
                        {

                            List<string> todo = ffLplan;

                            foreach (string act in todo)
                            {
                                agentState[agent.name] = agentState[agent.name].ApplyII(agents[map[agent.name]].domain.mapActionNameToAction[act]);
                                finalPlan.Add(act);
                                foreach (Agent a in agents)
                                {
                                    if (!a.name.Equals(agent.name))
                                    {

                                        agentState[a.name] = agentState[a.name].ApplyEffect(agents[map[agent.name]].domain.mapActionNameToAction[act], a.Predicates);
                                    }
                                }
                            }
                        }
                        else
                        {
                            Program.KillPlanners();
                            return GroundingActions(out finalPlan, out fault);

                        }
                    }
                }
            }
            foreach (var agSt in agentState)
            {
                if (agSt.Value == null)
                {
                    Program.KillPlanners();
                    return false;

                }
            }

            return true;


        }
        public bool IsDeadEnd()
        {
            foreach (Agent agent in agents)
            {
                agent.SetLandmarkToExplorer((Landmark)null);

            }


            HashSet<GroundedPredicate> publicSet = new HashSet<GroundedPredicate>();

            foreach (Agent agent in agents)
            {
                HashSet<GroundedPredicate> tmp = agent.DetectionFrom(statesNubmber.ElementAt(map[agent.name]));
                foreach (var gp in tmp)
                {
                    if (!publicSet.Contains(gp))
                    {
                        publicSet.Add(gp);
                    }
                }
            }

            bool flag2 = true;
            while (flag2)
            {
                flag2 = false;
                foreach (Agent agent in agents)
                {

                    HashSet<GroundedPredicate> tmp = agent.WhatYoCanGet(publicSet);

                    foreach (var gp in tmp)
                    {
                        if (!publicSet.Contains(gp))
                        {
                            publicSet.Add(gp);
                            flag2 = true;
                        }
                    }
                }

            }
            List<bool[]> vecAns = new List<bool[]>();
            foreach (Agent agent in agents)
            {
                vecAns.Add(agent.PotentialToAchieve(goals));
            }
            bool flag;
            for (int i = 0; i < vecAns.ElementAt(0).Length; i++)
            {
                flag = false;
               
                    foreach (bool[] vec in vecAns)
                    {
                        if (vec[i])
                        {
                            flag = true;
                            break;
                        }
                    }
                    if (!flag)
                        return true;
                
            }
            return false;
        }


        
        
        public static int Comparer(PdbVertex v1, PdbVertex v2)
        {
            if (v1.h == v2.h)
            {
                if (v1.g == v2.g)
                {
                    bool v1Win = false;
                    bool v2Win = false;
                    // if(!v1.Equals(v2))
                    /*  
                      if (v1.lplan.Count > 1 && v1.lplan[v1.lplan.Count - 1].Key.Equals(v1.lplan[v1.lplan.Count - 2].Key))
                      {
                          v1Win=true;
                      }
                      if (v2.lplan.Count > 1 && v2.lplan[v2.lplan.Count - 1].Key.Equals(v2.lplan[v2.lplan.Count - 2].Key))
                      {
                          v2Win = true;
                      }
                      if(v1Win && !v2Win)
                      {
                          return -1;
                      }
                      if (!v1Win && v2Win)
                      {
                          return 1;
                      }
                      /*if (v1.cost > v2.cost)
                          return 1;
                      if (v1.cost < v2.cost)
                          return -1;*/

                    return 0;
                }
                if (v1.g > v2.g)
                    return 1;
                else
                    return -1;



            }
            if (v1.h > v2.h) return 1;
            return -1;

        }

        public static int ComparerDouble(double v1, double v2)
        {
            if (v1 > v2) return 1;
            if (v1 > v2) return -1;
            return 0;

        }
        public static int ComparerOp(PdbVertex v1, PdbVertex v2)
        {
            if (v1.h == v2.h)
            {
                if (v1.g == v2.g)
                {
                    /*if (v1.cost > v2.cost)
                        return 1;
                    if (v1.cost < v2.cost)
                        return -1;*/

                    return 0;
                }
                if (v1.g > v2.g)
                    return -1;
                else
                    return 1;



            }
            if (v1.h > v2.h) return -1;
            return 1;

        }


        public static int ComparerII(PdbVertex v1, PdbVertex v2)
        {
            if ((v1.h + v1.g) == (v2.h + v2.g))
            {
                if (v1.h == v2.h)
                    return 0;
                if (v1.h > v2.h)
                    return 1;
                else
                    return -1;



            }
            if ((v1.h + v1.g) > (v2.h + v2.g)) return 1;
            return -1;

        }
        public static List<string> ReadPlan(MemoryStream ms)
        {
            List<string> lPlan = new List<string>();

            StreamReader sr = new StreamReader(ms);

            while (!sr.EndOfStream)
            {
                string sAction = sr.ReadLine().Trim().ToLower();
                if (sAction != "")
                    lPlan.Add(sAction);
            }
            sr.Close();
            return lPlan;



            List<string> lFilteredPlan = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.Contains("-remove") ||
                    sAction.Contains("-translate"))
                    continue;
                if (sAction.Contains("-add"))
                    lFilteredPlan.Add(sAction.Replace("-add", ""));
                else
                    lFilteredPlan.Add(sAction);

            }

            return lFilteredPlan;
        }
        public static List<string> Plan(Domain d, Problem p, State curentState, Formula goal, List<Action> privateActions)
        {
            List<string> lPlan = new List<string>();



            d.Actions = privateActions;
            p.Goal = goal;

            MemoryStream msDomain = d.WriteSimpleDomain();
            MemoryStream problem_M_S = p.WriteSimpleProblem(curentState);




            Process planer = new Process();
            //planer.StartInfo.WorkingDirectory = @"C:\project\Planning 2 new\PDDLTEST\temp";
            planer.StartInfo.FileName = "ff.exe";
            //planer.StartInfo.Arguments += "-o dT.pddl -f pT.pddl";

            planer.StartInfo.UseShellExecute = false;
            planer.StartInfo.RedirectStandardInput = true;
            planer.StartInfo.RedirectStandardOutput = true;
            planer.Start();
            StreamReader srOps = new StreamReader(msDomain);


            planer.StandardInput.Write(srOps.ReadToEnd());
            srOps.Close();
            BinaryWriter b = new BinaryWriter(planer.StandardInput.BaseStream);
            b.Write('\0');

            StreamReader srFct = new StreamReader(problem_M_S);
            planer.StandardInput.Write(srFct.ReadToEnd());
            srFct.Close();

            b.Write('\0');
            //planer.StandardInput.Flush();

            planer.StandardInput.Close();

            /* if (!planer.WaitForExit(4000))//2 minutes max
             {
                 planer.Kill();
             }*/

            string sOutput = planer.StandardOutput.ReadToEnd();
            //Console.WriteLine(sOutput);
            MemoryStream planMs = new MemoryStream();
            if (sOutput.Contains("found legal plan as follows"))
            {
                string sPlan = sOutput.Substring(sOutput.IndexOf("found legal plan as follows"));
                string[] asPlan = sPlan.Split('\n');
                string sFinalPlan = "";
                for (int i = 2; i < asPlan.Length; i++)
                {
                    if (!asPlan[i].Contains(":"))
                        break;
                    sFinalPlan += asPlan[i].Substring(asPlan[i].IndexOf(':') + 2).Trim() + "\n";
                }
                StreamWriter sw = new StreamWriter(planMs);
                sw.WriteLine(sFinalPlan);
                sw.Close();
            }
            else if (sOutput.Contains("goal can be simplified to TRUE"))
                return new List<string>();
            else
            {
                return null;
            }


            lPlan = ReadPlan(new MemoryStream(planMs.ToArray()));
            return lPlan;
        }
        private bool Contains(State x, List<Predicate> y)
        {
            if (y == null)
                return true;
            if (x == null)
            {
                if (y.Count == 0)
                    return true;
                return false;
            }
            foreach (GroundedPredicate gP in y)
            {
                if (!x.m_lPredicates.Contains(gP)) return false;
            }
            return true;
        }
        public static List<string> ReadPlan(string sPath)
        {
            List<string> lPlan = new List<string>();
            string sPlanFile = "plan.txt";
            if (File.Exists(sPath + sPlanFile))
            {
                StreamReader sr = new StreamReader(sPath + sPlanFile);
                while (!sr.EndOfStream)
                {
                    string sAction = sr.ReadLine().Trim().ToLower();
                    if (sAction != "")
                        lPlan.Add(sAction);
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "mipsSolution.soln"))
            {
                StreamReader sr = new StreamReader(sPath + "mipsSolution.soln");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        int iEnd = sLine.IndexOf(")");
                        sLine = sLine.Substring(iStart + 1, iEnd - iStart - 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "sas_plan"))
            {
                StreamReader sr = new StreamReader(sPath + "sas_plan");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    sLine = sLine.Replace("(", "");
                    sLine = sLine.Replace(")", "");
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        sLine = sLine.Substring(iStart + 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else
            {
                /*
                if (SDRPlanner.AddTagRefutationToGoal)
                {
                    SDRPlanner.AddTagRefutationToGoal = false;
                    lPlan = Plan(sPath, pssCurrent, out sChosen);
                }
                else
                 * */

                //throw new Exception("ended");

                return null;
            }

            List<string> lFilteredPlan = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.Contains("-remove") ||
                    sAction.Contains("-translate"))
                    continue;
                if (sAction.Contains("-add"))
                    lFilteredPlan.Add(sAction.Replace("-add", ""));
                else
                    lFilteredPlan.Add(sAction);

            }

            return lFilteredPlan;
        }

        public static List<string> Plan2(Domain d, Problem p, State curentState, Formula goal, List<Action> privateActions)
        {
            List<string> lPlan = new List<string>();
            d.Actions = privateActions;
            DirectoryInfo di = new DirectoryInfo(@"C:\project\Planning 2 new\PDDLTEST\temp\");
            foreach (FileInfo fi in di.GetFiles())
                if ((fi.Name.StartsWith("pT") || fi.Name.StartsWith("plan")))// && fi.Name.EndsWith(".pddl"))
                    fi.Delete();

            d.WriteSimpleDomain(@"C:\project\Planning 2 new\PDDLTEST\temp\dT.pddl");
            p.Goal = goal;
            p.WriteSimpleProblem(@"C:\project\Planning 2 new\PDDLTEST\temp\pT.pddl", curentState);




            Process planer = new Process();
            planer.StartInfo.WorkingDirectory = @"C:\project\Planning 2 new\PDDLTEST\temp";
            planer.StartInfo.FileName = "ff.exe";
            planer.StartInfo.Arguments += "-o dT.pddl -f pT.pddl";
            planer.StartInfo.UseShellExecute = false;
            planer.StartInfo.RedirectStandardOutput = true;
            planer.Start();
            if (!planer.WaitForExit(10000000))//2 minutes max
            {
                planer.Kill();
            }
            lPlan = ReadPlan(@"C:\project\Planning 2 new\PDDLTEST\temp\");
            return lPlan;
        }
        public static void FF_Plan(Domain d, Problem p, State curentState, Formula goal, List<Action> privateActions)
        {
            List<string> lPlan = new List<string>();



            d.Actions = privateActions;
            p.Goal = goal;

            MemoryStream msDomain = d.WriteSimpleDomain();
            MemoryStream problem_M_S = p.WriteSimpleProblem(curentState);




            Process planer = new Process();
            //planer.StartInfo.WorkingDirectory = @"C:\project\Planning 2 new\PDDLTEST\temp";
            planer.StartInfo.FileName = "ff.exe";
            //planer.StartInfo.Arguments += "-o dT.pddl -f pT.pddl";

            planer.StartInfo.UseShellExecute = false;
            planer.StartInfo.RedirectStandardInput = true;
            planer.StartInfo.RedirectStandardOutput = true;
            planer.Start();
            StreamReader srOps = new StreamReader(msDomain);


            planer.StandardInput.Write(srOps.ReadToEnd());
            srOps.Close();
            BinaryWriter b = new BinaryWriter(planer.StandardInput.BaseStream);
            b.Write('\0');

            StreamReader srFct = new StreamReader(problem_M_S);
            planer.StandardInput.Write(srFct.ReadToEnd());
            srFct.Close();

            b.Write('\0');
            //planer.StandardInput.Flush();

            planer.StandardInput.Close();

            /*if (!planer.WaitForExit(9000))//2 minutes max
            {
                planer.Kill();
            }*/

            string sOutput = planer.StandardOutput.ReadToEnd();
            //Console.WriteLine(sOutput);
            MemoryStream planMs = new MemoryStream();
            if (sOutput.Contains("found legal plan as follows"))
            {
                string sPlan = sOutput.Substring(sOutput.IndexOf("found legal plan as follows"));
                string[] asPlan = sPlan.Split('\n');
                string sFinalPlan = "";
                for (int i = 2; i < asPlan.Length; i++)
                {
                    if (!asPlan[i].Contains(":"))
                        break;
                    sFinalPlan += asPlan[i].Substring(asPlan[i].IndexOf(':') + 2).Trim() + "\n";
                }
                StreamWriter sw = new StreamWriter(planMs);
                sw.WriteLine(sFinalPlan);
                sw.Close();
            }
            else
            {
                if (sOutput.Contains("goal can be simplified to TRUE"))
                {
                    ffLplan = new List<string>();
                    return;
                }
                else
                {

                    ffLplan = null;
                    return;

                }
            }


            lPlan = ReadPlan(new MemoryStream(planMs.ToArray()));
            ffLplan = lPlan;
            return;

        }

        public override bool Equals(object obj)
        {
            if (obj is Vertex)
            {
                Vertex v = (Vertex)obj;
                if (JointPublicPredicates.Count != v.JointPublicPredicates.Count)
                    return false;
                foreach (Predicate p in JointPublicPredicates)
                    if (!v.JointPublicPredicates.Contains(p))
                        return false;
                return true;
            }
            return false;
        }
        int m_iHashCode = 0;
        public override int GetHashCode()
        {
            if (m_iHashCode == 0)
            {
                foreach (Predicate p in JointPublicPredicates)
                    m_iHashCode += p.GetHashCode();
            }
            return m_iHashCode;
        }
        public override string ToString()
        {
            return ID + " h = " + h + " g = " + g;
        }

    }




    class ComaparePdbVertex : IComparer<PdbVertex>
    {
        public static IComparer<PdbVertex> GetVertexComparer()
        {
            return (IComparer<PdbVertex>)new ComapareVertex();
        }

        int IComparer<PdbVertex>.Compare(PdbVertex vertex1, PdbVertex vertex2)
        {
            PdbVertex v1 = (PdbVertex)vertex1;
            PdbVertex v2 = (PdbVertex)vertex2;

            if (v1.h == v2.h)
            {
                if (v1.g == v2.g)
                {

                    return 0;
                }
                if (v1.g > v2.g)
                    return 1;
                else
                    return -1;



            }
            if (v1.h > v2.h) return 1;
            return -1;
        }


    }
}
