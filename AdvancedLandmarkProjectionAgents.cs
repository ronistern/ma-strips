using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;

namespace Planning
{
    static class AdvancedLandmarkProjectionAgents
    {
        public static List<string> lplan;
        public static Dictionary<string,int> map=null;
        public static Dictionary<string, Action> mapActionNameToAction = null;
        public static List<Agent> agents = null;
        public static List<string> highLevelplan;
        public static List<string> ffLplan = null;
        public static List<Agent> CreateProjAgents(List<Agent> m_agents, List<Domain> lDomains, List<Problem> lProblems)
        {
            agents = m_agents;
            map = new Dictionary<string, int>();
            int j = 0;
            foreach(Agent agent in agents)
            {
                map.Add(agent.name, j);
                j++;
            }
            List<Action> allProjectionAction = new List<Action>();
            List<Landmark> lGoal = new List<Landmark>();
            int index = 0;
            Distributed_Landmarks_Detection.Reset(agents);
            List<Predicate> predicates = new List<Predicate>();
            Domain dPublic = new Domain("PublicDomain", "");
            Problem pPublic = new Problem("PublicProblem", dPublic);
            State publicStartState = new State(pPublic);
            GroundedPredicate newPrePredicate = null;
            newPrePredicate = new GroundedPredicate(Domain.ARTIFICIAL_PREDICATE+"StartState");
            publicStartState.AddPredicate(newPrePredicate);
            predicates.Add(newPrePredicate);
            //mapActionNameToAction=new Dictionary<string,Action>();

            for (int i = 0; i < agents.Count;i++ )
            {
                Agent agent = agents[i];
                agent.mapActionNameToAction = new Dictionary<string, Action>();
                foreach (Action act in agent.publicActions)
                {
                    if (!agent.mapActionNameToAction.ContainsKey(act.Name))
                        agent.mapActionNameToAction.Add(act.Name, act);
                }
                agent.initLandmarksDetect();
                agent.saveInfo();
                State startState = new State(lProblems[i]);
                startState.AddPredicate(newPrePredicate);
                List<Action> currentlProjAction = agent.getAdvancedProjectionPublicAction(index, predicates, startState);
                agent.m_actions = currentlProjAction;
                agent.privateActions = new List<Action>();
                agent.publicActions = currentlProjAction;
               // agent.PublicPredicates = new HashSet<GroundedPredicate>();
                
                //allProjectionAction.AddRange(currentlProjAction);
                
                foreach (Action act in currentlProjAction)
                {
                    act.agent = agent.name;
                    //if (!agent.mapActionNameToAction.ContainsKey(act.Name))
                      //  agent.mapActionNameToAction.Add(act.Name, act);
                }
                foreach (Predicate pred in agent.PublicPredicates)
                {
                    predicates.Add(pred);
                 //   agent.PublicPredicates.Add((GroundedPredicate)pred);
                }
                agent.Predicates = new HashSet<GroundedPredicate>();
                foreach (GroundedPredicate pgp in predicates)
                {
                    agent.Predicates.Add(pgp);
                }

                foreach (GroundedPredicate pgp in agent.GetPublicStartState())
                {
                    startState.AddPredicate(pgp);
                }
                index += 1000;
                lGoal.AddRange(agent.GetPublicGoals());

                /**** I implmented this in GetPublicStartState function in Agent  ****/

                List<GroundedPredicate> lInitialPrivate = agent.GetPrivateStartState();
                foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> pArtificial in agent.ArtificialToPrivate)
                {
                    bool bAllTrue = true;
                    foreach (GroundedPredicate gpReal in pArtificial.Value)
                    {
                        if (!lInitialPrivate.Contains(gpReal))
                            bAllTrue = false;
                    }
                    if (bAllTrue)
                    {
                        if (!startState.Contains(pArtificial.Key))
                        {
                            startState.AddPredicate(pArtificial.Key);
                        }
                    }
                }
                agent.startState = startState;
            }
            return agents;
           /* dPublic.Actions = allProjectionAction;
            foreach (Domain d in lDomains)
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
            */
            
            /*CompoundFormula goalf = new CompoundFormula("and");
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

            highLevelplan = ExternalPlanners.FFPlan(dPublic, pPublic, publicStartState, goalf, dPublic.Actions, 20 * 60000, out ans);
            //highLevelplan = ExternalPlanners.FDPlan(dPublic, pPublic, publicStartState, goalf, dPublic.Actions, 20 * 60000, out ans);
            if (highLevelplan == null)
                return null;
            //    return ManualSolve(pPublic, dPublic);
            string fault;
            List<string> finalPlan;
            if (Grounding(out finalPlan, out fault))
                return finalPlan;
            //throw new NotImplementedException();
            return null;*/

        }

        private static List<string> GeneratePlan(State sBeforeLast, Action aLast, Dictionary<State, State> dParents, Dictionary<State, Action> dMapStateToGeneratingAction)
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



        public static bool Grounding(out List<string> finalPlan, out string fault)
        {
            Console.WriteLine("\nPublic global plan found, searching for private plans");
            List<Dictionary<CompoundFormula, string>> newPlan = new List<Dictionary<CompoundFormula, string>>();
            List<KeyValuePair<string, CompoundFormula>> lplan = new List<KeyValuePair<string, CompoundFormula>>();
            foreach (string actname in highLevelplan)
            {
                Action act = mapActionNameToAction[actname];
                CompoundFormula effect = new CompoundFormula("and");
                foreach (GroundedPredicate gp in act.HashEffects)
                {
                    if (agents[map[act.agent]].PublicPredicates.Contains(gp))
                        effect.AddOperand(gp);
                }
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

                HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
                foreach (GroundedPredicate gp in goalFormula.GetAllPredicates())
                {
                    if (agents[map[agentName]].MutuallyExclusive.ContainsKey(gp))
                    {
                        foreach (GroundedPredicate mgp in agents[map[agentName]].MutuallyExclusive[gp])
                            mutex.Add(mgp);
                    }
                }
                /*
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
                        //return planToGoalIIII(out finalPlan, out fault);

                    }
                }
            }
            foreach (var agSt in agentState)
            {
                if (agSt.Value == null) return false;
            }

            return true;


        }
    }
}
