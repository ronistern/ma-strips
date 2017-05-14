using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;

namespace Planning
{
    class AdvancedProjectionHeuristic
    {
        public static bool threadContinueSearchFlag = true;
        public static Mutex mutex = new Mutex();
        public static Mutex mutex2 = new Mutex();
        public List<bool> threadAns = null;
        HashSet<GroundedPredicate> allKindOfpublicPreconditions = null;
        public List<string> lplan;
        public Dictionary<string, int> map = null;
        public Dictionary<string, Action> mapActionNameToAction = null;
        public List<Agent> agents = null;
        public List<string> highLevelplan;
        public List<Action> allProjectionAction = null;
        public List<Predicate> predicates = null;
        public State basicStartState = null;
        public enum GroundingType { MultiThreading, MinimalLocalsPlan, RegularGrounding, ActionGrounding };
        GroundingType groundingType = GroundingType.MultiThreading;
        public List<string> ffLplan = null;
        State globalInitialState = null;
        List<Domain> m_lDomains = null;
        public List<Landmark> lGoal = null;
        public AdvancedProjectionHeuristic(Agent fullAgent, List<Agent> m_agents, List<Domain> lDomains, List<Problem> lProblems)
        {
            bool allEqual = true;
            if(Program.projectionVersion==Program.ProjectionVersion.ProjectionFF)
            {
                allEqual = false;
            }
            else
                if (Program.projectionVersion == Program.ProjectionVersion.GlobalV2)
                {
                    allEqual = false;
                }
            Domain dPublic = new Domain("PublicDomain", "");
            Problem pPublic = new Problem("PublicProblem", dPublic);
            basicStartState = new State(pPublic);
            GroundedPredicate newPrePredicate = null;
            newPrePredicate = new GroundedPredicate(Domain.ARTIFICIAL_PREDICATE + "StartState");
            basicStartState.AddPredicate(newPrePredicate);
            predicates = new List<Predicate>();
            predicates.Add(newPrePredicate);

            Program.countOfProjAction = 0;
            Program.countOfProjFact = 0;
            Program.sizeOfRegressionTree = 0;
            Program.maxSizeOfRegressionTree = 0;
            Program.maxDepthOfRegressionTree = 0;
            DateTime startTime = DateTime.Now;
            m_lDomains = lDomains;
            globalInitialState = new State((Problem)(null));
            Program.StartHighLevelPlanning = DateTime.Now;
            agents = m_agents;
            map = new Dictionary<string, int>();
            int j = 0;
            foreach (Agent agent in agents)
            {
                map.Add(agent.name, j);
                j++;
                foreach (GroundedPredicate gp in agent.startState.m_lPredicates)
                {
                    globalInitialState.AddPredicate(gp);
                }
            }

            allProjectionAction = new List<Action>();
            lGoal = new List<Landmark>();
            int index = 0;
            Distributed_Landmarks_Detection.Reset(agents);
            // predicates = new List<Predicate>();



            mapActionNameToAction = new Dictionary<string, Action>();
            allKindOfpublicPreconditions = new HashSet<GroundedPredicate>(); ;


            foreach (Agent agent in agents)
            {
                agent.initLandmarksDetect();

                foreach (Action act in agent.publicActions)
                {
                    foreach (GroundedPredicate preGp in act.Preconditions.GetAllPredicates())
                    {
                        allKindOfpublicPreconditions.Add(preGp);
                    }

                    if (!mapActionNameToAction.ContainsKey(act.Name))
                        mapActionNameToAction.Add(act.Name, act);
                }

                List<Action> currentlProjAction = null;
                if (allEqual || !agent.name.Equals(fullAgent.name))
                {
                    currentlProjAction = agent.getAdvancedProjectionPublicAction(index, predicates);
                }
                else
                {
                    if (Program.projectionVersion == Program.ProjectionVersion.ProjectionFF)
                    {
                        currentlProjAction = fullAgent.publicActions;
                    }
                    else
                        currentlProjAction = fullAgent.m_actions;
                }

                if (false && Program.projectionVersion == Program.ProjectionVersion.ProjectionFF && agent.name.Equals(fullAgent.name))
                {
                    int i = 0;
                    foreach(Action act in currentlProjAction)
                    {
                        allProjectionAction.Insert(i, act);
                        i++;
                    }
                }
                else
                    allProjectionAction.AddRange(currentlProjAction);

                foreach (GroundedPredicate goalGp in agent.goal)
                {
                    allKindOfpublicPreconditions.Add(goalGp);
                }

                foreach (Action act in currentlProjAction)
                {
                    act.agent = agent.name;
                    if (!mapActionNameToAction.ContainsKey(act.Name))
                        mapActionNameToAction.Add(act.Name, act);
                }

                if (allEqual || !agent.Equals(fullAgent))
                {
                    foreach (Predicate pred in agent.PublicPredicates)
                    {
                        predicates.Add(pred);
                    }
                }
                else
                {
                    foreach (Predicate pred in agent.Predicates)
                    {
                        predicates.Add(pred);
                    }
                }
                if (!agent.Equals(fullAgent))
                {
                    lGoal.AddRange(agent.GetPublicGoals());
                }
                else
                {
                    lGoal.AddRange(agent.GetPublicGoals());
                }


                index += 1000;


                /**** I implmented this in GetPublicStartState function in Agent  ****/
            }


            /*
                string fault;
                List<string> finalPlan = null;
                Program.StartGrounding = DateTime.Now;

                if (groundingType == GroundingType.MultiThreading)
                {
                    finalPlan = this.GetGroundPlan(joinDomain);
                }
                if (groundingType == GroundingType.MinimalLocalsPlan)
                {
                    RegTasksDistributionGrounding(out finalPlan, out fault);
                }
                if (groundingType == GroundingType.RegularGrounding)
                {
                    RegGrounding(out finalPlan, out fault);
                }
                if (groundingType == GroundingType.ActionGrounding)
                {
                    GroundingActions(out finalPlan, out fault);
                }

                return finalPlan;
               ;
                return null;*/
        }

        public static HSPHeuristic hsp = null;
        public static ForwardSearchPlanner forwardSearch = null;

        public int GethValue2(Agent fullAgent, List<HashSet<Predicate>> states, Dictionary<string, List<Action>> localsPlans, List<Action> allPlan, out int h)
        {
            h = 0;
            Domain dPublic = new Domain("PublicDomain", "");
            Problem pPublic = new Problem("PublicProblem", dPublic);
            State publicStartState = new State(pPublic);
            publicStartState.m_lPredicates.UnionWith(basicStartState.m_lPredicates);
            foreach (HashSet<Predicate> ps in states)
            {
                publicStartState.m_lPredicates.UnionWith(ps);
            }

            /*foreach (Agent agent in agents)
            {
                foreach (GroundedPredicate pgp in agent.GetPublicStartState())
                {
                    publicStartState.AddPredicate(pgp);
                }
            }*/

            dPublic.Actions = allProjectionAction;
            foreach (Domain d in m_lDomains)
            {
                foreach (ParametrizedPredicate pp in d.Predicates)
                    dPublic.Predicates.Add(pp);
                foreach (string sType in d.Types)
                    if (!dPublic.Types.Contains(sType))
                        dPublic.Types.Add(sType);
                foreach (KeyValuePair<string, string> pair in d.TypeHierarchy)
                    dPublic.TypeHierarchy[pair.Key] = pair.Value;
                foreach (Constant c in d.Constants)
                    dPublic.Constants.Add(c);
            }
            foreach (Predicate p in predicates)
            {
                if (p.Name.StartsWith(Domain.ARTIFICIAL_PREDICATE))
                {
                    ParametrizedPredicate pp = new ParametrizedPredicate(p.Name);
                    dPublic.Predicates.Add(pp);
                }

            }

            foreach (Predicate pInit in publicStartState.Predicates)
                pPublic.AddKnown(pInit);

            CompoundFormula goalf = new CompoundFormula("and");
            foreach (Landmark l in lGoal)
            {
                CompoundFormula disjGoal = new CompoundFormula("or");
                foreach (GroundedPredicate gp in l.facts.Keys)
                {
                    disjGoal.AddOperand(gp);
                }
                goalf.AddOperand(disjGoal);
            }
            pPublic.Goal = goalf;

            bool ans;
            ExternalPlanners externalPlanners = new ExternalPlanners();
            //highLevelplan = externalPlanners.FFPlan(dPublic, pPublic, publicStartState, goalf, dPublic.Actions, 30 * 60000, out ans);
            // highLevelplan = externalPlanners.FDPlan(dPublic, pPublic, publicStartState, goalf, dPublic.Actions, 20 * 60000, out ans);
            List<Predicate> localGoal = new List<Predicate>();
            foreach (GroundedPredicate p in goalf.GetAllPredicates())
            {
                localGoal.Add(p);
            }
            highLevelplan = externalPlanners.Plan(true, true, dPublic, pPublic, publicStartState, goalf, dPublic.Actions, 5*60000, out ans);
            // hsp = new HSPHeuristic(dPublic.Actions, localGoal, false);
           //  forwardSearch = new ForwardSearchPlanner(dPublic.Actions, hsp);
           //  List<Action> highLevelplan = forwardSearch.Plan(publicStartState, localGoal);

            if (highLevelplan == null)
            {
                hsp = new HSPHeuristic(dPublic.Actions, localGoal, false);
                h = (int)hsp.h(publicStartState);
                return -1;
            }
            int heuristic = 0;

            heuristic = highLevelplan.Count;

            int sum = 0;

            foreach (var act in highLevelplan)
            {
               // Action action = act;
                Action action = mapActionNameToAction[act];
                allPlan.Add(action);
                localsPlans[action.agent].Add(action);
            }

            return heuristic;

        }
        public int GethValue(Agent fullAgent, List<HashSet<Predicate>> states, bool allValue, List<Action> localPlan)
        {
            Domain dPublic = new Domain("PublicDomain", "");
            Problem pPublic = new Problem("PublicProblem", dPublic);
            State publicStartState = new State(pPublic);
            publicStartState.m_lPredicates.UnionWith(basicStartState.m_lPredicates);
            foreach (HashSet<Predicate> ps in states)
            {
                publicStartState.m_lPredicates.UnionWith(ps);
            }

            /*foreach (Agent agent in agents)
            {
                foreach (GroundedPredicate pgp in agent.GetPublicStartState())
                {
                    publicStartState.AddPredicate(pgp);
                }
            }*/

            dPublic.Actions = allProjectionAction;
            foreach (Domain d in m_lDomains)
            {
                foreach (ParametrizedPredicate pp in d.Predicates)
                    dPublic.Predicates.Add(pp);
                foreach (string sType in d.Types)
                    if (!dPublic.Types.Contains(sType))
                        dPublic.Types.Add(sType);
                foreach (KeyValuePair<string, string> pair in d.TypeHierarchy)
                    dPublic.TypeHierarchy[pair.Key] = pair.Value;
                foreach (Constant c in d.Constants)
                    dPublic.Constants.Add(c);
            }
            foreach (Predicate p in predicates)
            {
                if (p.Name.StartsWith(Domain.ARTIFICIAL_PREDICATE))
                {
                    ParametrizedPredicate pp = new ParametrizedPredicate(p.Name);
                    dPublic.Predicates.Add(pp);
                }

            }

            foreach (Predicate pInit in publicStartState.Predicates)
                pPublic.AddKnown(pInit);

            CompoundFormula goalf = new CompoundFormula("and");
            foreach (Landmark l in lGoal)
            {
                CompoundFormula disjGoal = new CompoundFormula("or");
                foreach (GroundedPredicate gp in l.facts.Keys)
                {
                    disjGoal.AddOperand(gp);
                }
                goalf.AddOperand(disjGoal);
            }
            pPublic.Goal = goalf;

            bool ans;
            ExternalPlanners externalPlanners = new ExternalPlanners();
            //highLevelplan = externalPlanners.FFPlan(dPublic, pPublic, publicStartState, goalf, dPublic.Actions, 30 * 60000, out ans);
            // highLevelplan = externalPlanners.FDPlan(dPublic, pPublic, publicStartState, goalf, dPublic.Actions, 20 * 60000, out ans);
            List<Predicate> localGoal = new List<Predicate>();
            foreach (GroundedPredicate p in goalf.GetAllPredicates())
            {
                localGoal.Add(p);
            }

            // highLevelplan = externalPlanners.Plan(true, false, dPublic, pPublic, publicStartState, goalf, dPublic.Actions, 10 * 60000, out ans);
            hsp = new HSPHeuristic(dPublic.Actions, localGoal, false);
            forwardSearch = new ForwardSearchPlanner(dPublic.Actions, hsp);
            List<Action> highLevelplan = forwardSearch.Plan(publicStartState, localGoal);

            if (highLevelplan == null)
            {
                return int.MaxValue;
            }
            int heuristic = 0;
            if (allValue)
            {
                heuristic = highLevelplan.Count;
            }

            int sum = 0;
            foreach (var act in highLevelplan)
            {
                Action action = act;
                // Action action = mapActionNameToAction[act];
                if (action.agent == fullAgent.name)
                {
                    if (!allValue)
                        heuristic++;
                    if (localPlan != null)
                        localPlan.Add(action);
                }
            }
            return heuristic;

        }
       
        private List<string> GeneratePlan(State sBeforeLast, Action aLast, Dictionary<State, State> dParents, Dictionary<State, Action> dMapStateToGeneratingAction)
        {
            List<string> lPlan = new List<string>();
            State sCurrent = sBeforeLast;
            lPlan.Add(aLast.Name);
            while (dParents[sCurrent] != null)
            {
                Action a = dMapStateToGeneratingAction[sCurrent];
                lPlan.Add(a.Name);
                sCurrent = dParents[sCurrent];
            }
            lPlan.Reverse();
            return lPlan;
        }



        public bool Grounding(out List<string> finalPlan, out string fault)
        {
            Console.WriteLine("\nPublic global plan found, searching for private plans");
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
            foreach (string actname in highLevelplan)
            {
                Action act = mapActionNameToAction[actname];
                CompoundFormula effect = new CompoundFormula("and");
                bool flag = false;
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (agents[map[act.agent]].PublicPredicates.Contains(gp))
                    {
                        if (allKindOfpublicPreconditions.Contains(gp))
                        {
                            effect.AddOperand(gp);
                            flag = true;
                        }

                    }
                }
                if (flag)
                    lplan.Add(new KeyValuePair<string, CompoundFormula>(act.agent, effect));
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
            foreach (KeyValuePair<string, CompoundFormula> eff in lplan)
            {
                agentName = eff.Key;
                goalFormula = new CompoundFormula(eff.Value);

                /* HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
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
                         if (!mutex.Contains(publicPos) && !goalFormula.GetAllPredicates().Contains(publicPos.Negate()))
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
                    return RegGrounding(out finalPlan, out fault);
                }


            }
            Dictionary<string, CompoundFormula> agentGoal = new Dictionary<string, CompoundFormula>();

            foreach (Agent a in agents)
            {
                agentGoal.Add(a.name, new CompoundFormula("and"));
                foreach (GroundedPredicate goalPredicate in a.goal)
                {
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
            foreach (var agent in agents)
            {
                if (agentGoal[agent.name].Operands.Count > 0)
                {
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name]);
                    // hsp = new HSPHeuristic(agent.m_actions, agentGoal[agent.name].GetAllPredicates().ToList(), admisabiliy);
                    //  forwardSearch = new ForwardSearchPlanner(agent.m_actions, hsp);
                    // List<Action> todo = forwardSearch.Plan(agentState[agent.name], agentGoal[agent.name].GetAllPredicates().ToList());
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name], agent.m_actions);
                    bool bUnsolvable = false;
                    ExternalPlanners externalPlanners = new ExternalPlanners();
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
                        Program.KillPlanners();
                        return RegGrounding(out finalPlan, out fault);

                    }
                }
            }
            foreach (var agSt in agentState)
            {
                if (agSt.Value == null)
                {
                    Program.KillPlanners();
                    return RegGrounding(out finalPlan, out fault);
                }
            }

            return true;


        }
        public bool RegGrounding(out List<string> finalPlan, out string fault)
        {
            Console.WriteLine("\nPublic global plan found, searching for private plans");
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
            foreach (string actname in highLevelplan)
            {
                Action act = mapActionNameToAction[actname];
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
            foreach (KeyValuePair<string, CompoundFormula> eff in lplan)
            {
                agentName = eff.Key;
                goalFormula = new CompoundFormula(eff.Value);

                /* HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
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
                         if (!mutex.Contains(publicPos) && !goalFormula.GetAllPredicates().Contains(publicPos.Negate()))
                             goalFormula.AddOperand(publicPos);
                     }
                 }
                  * */
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

            foreach (Agent a in agents)
            {
                agentGoal.Add(a.name, new CompoundFormula("and"));
                foreach (GroundedPredicate goalPredicate in a.goal)
                {
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
            foreach (var agent in agents)
            {
                if (agentGoal[agent.name].Operands.Count > 0)
                {
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name]);
                    // hsp = new HSPHeuristic(agent.m_actions, agentGoal[agent.name].GetAllPredicates().ToList(), admisabiliy);
                    //  forwardSearch = new ForwardSearchPlanner(agent.m_actions, hsp);
                    // List<Action> todo = forwardSearch.Plan(agentState[agent.name], agentGoal[agent.name].GetAllPredicates().ToList());
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name], agent.m_actions);
                    bool bUnsolvable = false;
                    ExternalPlanners externalPlanners = new ExternalPlanners();
                    ffLplan = externalPlanners.Plan(true, true, agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);

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
        public bool TasksDistributionGrounding(out List<string> finalPlan, out string fault)
        {
            Console.WriteLine("\nPublic global plan found, searching for private plans");
            Program.StartGrounding = DateTime.Now;

            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
            foreach (string actname in highLevelplan)
            {
                Action act = mapActionNameToAction[actname];
                CompoundFormula effect = new CompoundFormula("and");
                bool flag = false;
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (agents[map[act.agent]].PublicPredicates.Contains(gp))
                    {
                        if (allKindOfpublicPreconditions.Contains(gp))
                        {
                            effect.AddOperand(gp);
                            flag = true;
                        }
                        /* else
                         {
                             Console.Write("*");
                         }*/

                    }
                }
                if (flag)
                    lplan.Add(new KeyValuePair<string, CompoundFormula>(act.agent, effect));
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
            int iStep = 0;
            foreach (KeyValuePair<string, CompoundFormula> eff in lplan)
            {
                iStep++;
                // Console.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" + iStep + "/" + lplan.Count);
                agentName = eff.Key;
                goalFormula = new CompoundFormula(eff.Value);

                /*HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
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
                        if (!mutex.Contains(publicPos) && !goalFormula.GetAllPredicates().Contains(publicPos.Negate()))
                            goalFormula.AddOperand(publicPos);
                    }
                }
                 * */
                bool bUnsolvable = false;
                List<List<string>> localPlans = new List<List<string>>();
                foreach (Agent agent in agents)
                {
                    agentName = agent.name;
                    ExternalPlanners externalPlanners = new ExternalPlanners();
                    ffLplan = externalPlanners.FFPlan(agents[map[agentName]].domain, agents[map[agentName]].problem, agentState[agentName], goalFormula, agents[map[agentName]].m_actions, 5 * 60 * 1000, out bUnsolvable);

                    localPlans.Add(ffLplan);

                }
                //ffLplan = ExternalPlanners.FFPlan(agents[map[agentName]].domain, agents[map[agentName]].problem, agentState[agentName], goalFormula, agents[map[agentName]].m_actions, 5 * 60 * 1000, out bUnsolvable);
                int min = 10000;

                for (int i = 0; i < agents.Count; i++)
                {
                    if (localPlans[i] != null && localPlans[i].Count < min)
                    {
                        min = localPlans[i].Count;
                        ffLplan = localPlans[i];
                        agentName = agents[i].name;
                    }
                }
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
                    return RegTasksDistributionGrounding(out finalPlan, out fault);
                }


            }
            Dictionary<string, CompoundFormula> agentGoal = new Dictionary<string, CompoundFormula>();

            foreach (Agent a in agents)
            {
                agentGoal.Add(a.name, new CompoundFormula("and"));
                foreach (GroundedPredicate goalPredicate in a.goal)
                {
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
            foreach (var agent in agents)
            {
                if (agentGoal[agent.name].Operands.Count > 0)
                {
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name]);
                    // hsp = new HSPHeuristic(agent.m_actions, agentGoal[agent.name].GetAllPredicates().ToList(), admisabiliy);
                    //  forwardSearch = new ForwardSearchPlanner(agent.m_actions, hsp);
                    // List<Action> todo = forwardSearch.Plan(agentState[agent.name], agentGoal[agent.name].GetAllPredicates().ToList());
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name], agent.m_actions);
                    bool bUnsolvable = false;
                    ExternalPlanners externalPlanners = new ExternalPlanners();
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

                        Program.KillPlanners();
                        return RegTasksDistributionGrounding(out finalPlan, out fault);
                        //return planToGoalIIII(out finalPlan, out fault);

                    }
                }
            }
            foreach (var agSt in agentState)
            {
                if (agSt.Value == null)
                {
                    Program.KillPlanners();
                    return RegTasksDistributionGrounding(out finalPlan, out fault);
                }
            }

            return true;


        }
        public bool RegTasksDistributionGrounding(out List<string> finalPlan, out string fault)
        {
            Console.WriteLine("\nPublic global plan found, searching for private plans");
            Program.StartGrounding = DateTime.Now;

            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
            foreach (string actname in highLevelplan)
            {
                Action act = mapActionNameToAction[actname];
                CompoundFormula effect = new CompoundFormula("and");
                bool flag = false;
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (agents[map[act.agent]].PublicPredicates.Contains(gp))
                    {
                        //if (allKindOfpublicPreconditions.Contains(gp))
                        {
                            effect.AddOperand(gp);
                            flag = true;
                        }

                    }
                }
                if (flag)
                    lplan.Add(new KeyValuePair<string, CompoundFormula>(act.agent, effect));
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
            int iStep = 0;
            foreach (KeyValuePair<string, CompoundFormula> eff in lplan)
            {
                iStep++;
                // Console.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" + iStep + "/" + lplan.Count);
                agentName = eff.Key;
                goalFormula = new CompoundFormula(eff.Value);

                /*HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
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
                        if (!mutex.Contains(publicPos) && !goalFormula.GetAllPredicates().Contains(publicPos.Negate()))
                            goalFormula.AddOperand(publicPos);
                    }
                }
                 * */
                bool bUnsolvable = false;
                List<List<string>> localPlans = new List<List<string>>();
                foreach (Agent agent in agents)
                {
                    agentName = agent.name;
                    ExternalPlanners externalPlanners = new ExternalPlanners();
                    ffLplan = externalPlanners.FFPlan(agents[map[agentName]].domain, agents[map[agentName]].problem, agentState[agentName], goalFormula, agents[map[agentName]].m_actions, 5 * 60 * 1000, out bUnsolvable);

                    localPlans.Add(ffLplan);

                }
                //ffLplan = ExternalPlanners.FFPlan(agents[map[agentName]].domain, agents[map[agentName]].problem, agentState[agentName], goalFormula, agents[map[agentName]].m_actions, 5 * 60 * 1000, out bUnsolvable);
                int min = 10000;

                for (int i = 0; i < agents.Count; i++)
                {
                    if (localPlans[i] != null && localPlans[i].Count < min)
                    {
                        min = localPlans[i].Count;
                        ffLplan = localPlans[i];
                        agentName = agents[i].name;
                    }
                }
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
                    return Grounding(out finalPlan, out fault);
                }


            }
            Dictionary<string, CompoundFormula> agentGoal = new Dictionary<string, CompoundFormula>();

            foreach (Agent a in agents)
            {
                agentGoal.Add(a.name, new CompoundFormula("and"));
                foreach (GroundedPredicate goalPredicate in a.goal)
                {
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
            foreach (var agent in agents)
            {
                if (agentGoal[agent.name].Operands.Count > 0)
                {
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name]);
                    // hsp = new HSPHeuristic(agent.m_actions, agentGoal[agent.name].GetAllPredicates().ToList(), admisabiliy);
                    //  forwardSearch = new ForwardSearchPlanner(agent.m_actions, hsp);
                    // List<Action> todo = forwardSearch.Plan(agentState[agent.name], agentGoal[agent.name].GetAllPredicates().ToList());
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name], agent.m_actions);
                    bool bUnsolvable = false;
                    ExternalPlanners externalPlanners = new ExternalPlanners();
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

                        Program.KillPlanners();
                        return Grounding(out finalPlan, out fault);
                        //return planToGoalIIII(out finalPlan, out fault);

                    }
                }
            }
            foreach (var agSt in agentState)
            {
                if (agSt.Value == null)
                {
                    Program.KillPlanners();
                    return Grounding(out finalPlan, out fault);
                }
            }

            return true;


        }
        public bool GroundingActions(out List<string> finalPlan, out string fault)
        {
            Console.WriteLine("\nPublic global plan found, searching for private plans");
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<Action> lplan = new List<Action>();
            foreach (string actname in highLevelplan)
            {
                Action act = mapActionNameToAction[actname];
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

            foreach (Agent a in agents)
            {
                agentGoal.Add(a.name, new CompoundFormula("and"));
                foreach (GroundedPredicate goalPredicate in a.goal)
                {
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

            }
            foreach (var agent in agents)
            {
                if (agentGoal[agent.name].Operands.Count > 0)
                {
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name]);
                    // hsp = new HSPHeuristic(agent.m_actions, agentGoal[agent.name].GetAllPredicates().ToList(), admisabiliy);
                    //  forwardSearch = new ForwardSearchPlanner(agent.m_actions, hsp);
                    // List<Action> todo = forwardSearch.Plan(agentState[agent.name], agentGoal[agent.name].GetAllPredicates().ToList());
                    //List<string> todo = Plan(d, p, agentState[agent.name], agentGoal[agent.name], agent.m_actions);
                    bool bUnsolvable = false;
                    ExternalPlanners externalPlanners = new ExternalPlanners();
                    ffLplan = externalPlanners.Plan(true, true, agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);

                    //  ffLplan = externalPlanners.FFPlan(agents[map[agent.name]].domain, agents[map[agent.name]].problem, agentState[agent.name], agentGoal[agent.name], agent.m_actions, 5 * 60 * 1000, out bUnsolvable);
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
                        return false;
                        //return planToGoalIIII(out finalPlan, out fault);

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

        public List<string> GetGroundPlan(Domain joinDomain)
        {
            // Console.WriteLine("\nPublic global plan found, searching for private plans");
            List<string> finalPlan = new List<string>();
            threadContinueSearchFlag = true;
            Dictionary<string, State> agentState = new Dictionary<string, State>();
            Dictionary<int, List<string>> dicFinalPlan = new Dictionary<int, List<string>>();
            try
            {
                List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
                foreach (string actname in highLevelplan)
                {
                    Action act = mapActionNameToAction[actname];
                    CompoundFormula effect = new CompoundFormula("and");
                    bool flag = false;
                    foreach (GroundedPredicate gp in act.HashEffects)
                    {
                        if (agents[map[act.agent]].PublicPredicates.Contains(gp))
                        {
                            //if (allKindOfpublicPreconditions.Contains(gp))
                            {
                                effect.AddOperand(gp);
                                flag = true;
                            }

                        }
                    }
                    if (flag)
                        lplan.Add(new KeyValuePair<string, CompoundFormula>(act.agent, effect));
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
                    string f;
                    List<string> path = null;
                    RegGrounding(out path, out f);
                    return path;
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
                            string f;
                            List<string> path = null;
                            RegGrounding(out path, out f);
                            return path;

                        }
                    }
                }
                foreach (var agSt in agentState)
                {
                    if (agSt.Value == null)
                    {
                        string f;
                        List<string> path = null;
                        RegGrounding(out path, out f);
                        return path;
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

                return finalPlan;
            }
            catch (Exception ex)
            {
                string f;
                List<string> path = null;
                RegGrounding(out path, out f);
                return path;
            }
        }
    }
}
