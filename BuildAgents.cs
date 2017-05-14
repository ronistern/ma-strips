using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class BuildAgents
    {
        Problem problem = null;
        Domain domain = null;
        
        public Dictionary<string, HashSet<GroundedPredicate>> agentPredicate = new Dictionary<string,HashSet<GroundedPredicate>>();
        public Dictionary<GroundedPredicate, List<string>> agentEffPredicate = new Dictionary<GroundedPredicate,List<string>>();
        public Dictionary<string, HashSet<GroundedPredicate>> publicAgentPredicate = new Dictionary<string, HashSet<GroundedPredicate>>();
        List<Action> groundedAction = new List<Action>();
        private Dictionary<string, List<Action>> agentActions = new Dictionary<string, List<Action>>();
        private Dictionary<string, List<Action>> publicAgentActions = new Dictionary<string, List<Action>>();
        private Dictionary<string, List<Action>> privateAgentActions = new Dictionary<string, List<Action>>();
        public List<Action> publicAction = null;
        public List<Action> privateAction = null;
        Dictionary<string, List<Action>> agentActionl;
        int numberOfAgent=-1;
        Dictionary<Predicate, List<string>> sharePublicPredicate = new Dictionary<Predicate, List<string>>();
        Dictionary<Predicate, List<string>> canGetPublicPredicate = new Dictionary<Predicate, List<string>>();
        Dictionary<string, State> agentsStartState = new Dictionary<string, State>();
        Dictionary<string, List<GroundedPredicate>> agentsGoal = new Dictionary<string, List<GroundedPredicate>>();
        List<Agent> agents = new List<Agent>();
        public BuildAgents(Problem p, Domain d,string par)
        {
            problem = p;
            domain = d;
            groundedAction = domain.GroundAllActions(p);
            DivideActions(groundedAction,par);
            FindPublicAndPrivateAction(out publicAction, out privateAction);
            
            DivideStartState();
            DivideGoal();
            //HarderProblemsAlg hpal = new HarderProblemsAlg(p, d);
            foreach (var agentName in agentPredicate.Keys)
            {
                if (!agentsGoal.ContainsKey(agentName))
                {
                    agentsGoal.Add(agentName, new List<GroundedPredicate>());
                }
                Agent agent = new Agent(p, d, agentActions[agentName], publicAgentActions[agentName], privateAgentActions[agentName], agentPredicate[agentName], publicAgentPredicate[agentName], agentsStartState[agentName], agentsGoal[agentName], agentName, getProjectionPublicActionForAgent(agentName), null);
                agents.Add(agent);
            }
        }

        public List<Agent> ReturnAgents()
        {
            return agents;
        }
        public  List<Agent> CreateAgents()
        {
            return null;
        }

        private void DivideStartState()
        {
            
            
            foreach (var pair in agentPredicate)
            {
                agentsStartState.Add(pair.Key, new State(problem));
                foreach (GroundedPredicate gp in problem.Known)
                {
                    if (pair.Value.Contains(gp))
                    {
                        agentsStartState[pair.Key].AddPredicate(gp);
                    }
                }
            }
        }

        private void DivideGoal()
        {
            
                //agentsStartState.Add(pair.Key, new List<GroundedPredicate>());
                foreach (GroundedPredicate gp in problem.Goal.GetAllPredicates())
                {
                    List<string> agents=agentEffPredicate[gp];
                    foreach(var pair in agentsStartState)
                    {
                        if(pair.Value.Contains(gp))
                        {
                            if(!agents.Contains(pair.Key))
                            {
                                agents.Add(pair.Key);
                            }
                        }
                    }

                    bool publicGoal=false;
                    if(agents.Count>1)
                    {
                        publicGoal=true;
                      //  throw new NotImplementedException();
                    }
                    if (publicGoal)
                    {
                        gp.isPublic = true;
                    }
                    foreach(string agent in agents)
                    {
                        if(!agentsGoal.ContainsKey(agent))
                        {
                            agentsGoal.Add(agent,new List<GroundedPredicate>());
                             agentsGoal[agent].Add(gp);
                        }
                        else
                        {
                              agentsGoal[agent].Add(gp);
                        }
                    }
                }
            
        }

        private void DivideActions(List<Action> actions, string par)
        {
            agentPredicate = new Dictionary<string, HashSet<GroundedPredicate>>();
            List<Action> dell = new List<Action>();
            int fail = 0;
            foreach (Action act in actions)
            {
                if (((GroundedPredicate)act.HashEffects.ElementAt(0)).Name.Equals("P_FALSE"))
                {
                    dell.Add(act);
                    continue;
                }
                foreach (GroundedPredicate p in act.HashPrecondition)
                {
                    if (act.agent != null) break;
                    foreach (var arg in p.Constants)
                    {
                        bool f = false;
                        if (par.Equals("log"))
                        {
                            f = arg.Name.Contains("tru");
                        }
                        if ((arg.Name.Contains("rover") && arg.Name.Length == 6)  || arg.Name.Contains("fast") || arg.Name.Contains("slow") || arg.Name.Contains("plane") || arg.Name.Contains("apn") || arg.Name.Contains("satellite") || arg.Name.Contains("aircraft") || f)// || arg.Name.Contains("tru"))
                        {
                            act.agent = arg.Name;
                            if (!agentPredicate.ContainsKey(arg.Name))
                            {
                                agentPredicate.Add(arg.Name, new HashSet<GroundedPredicate>());
                                publicAgentActions.Add(arg.Name, new List<Action>());
                                publicAgentPredicate.Add(arg.Name, new HashSet<GroundedPredicate>());
                            }
                            break;
                        }
                        if ( act.Name.Contains("a0") )// || arg.Name.Contains("tru"))
                        {
                            act.agent = "a0";
                            if (!agentPredicate.ContainsKey(act.agent))
                            {
                                agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                publicAgentActions.Add(act.agent, new List<Action>());
                                publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                            }
                            break;
                        }
                        if (act.Name.Contains("a1"))// || arg.Name.Contains("tru"))
                        {
                            act.agent = "a1";
                            if (!agentPredicate.ContainsKey(act.agent))
                            {
                                agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                publicAgentActions.Add(act.agent, new List<Action>());
                                publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                            }
                            break;
                        }
                        if (act.Name.Contains("a2"))// || arg.Name.Contains("tru"))
                        {
                            act.agent = "a2";
                            if (!agentPredicate.ContainsKey(act.agent))
                            {
                                agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                publicAgentActions.Add(act.agent, new List<Action>());
                                publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                            }
                            break;
                        }
                        if (act.Name.Contains("a3"))// || arg.Name.Contains("tru"))
                        {
                            act.agent = "a3";
                            if (!agentPredicate.ContainsKey(act.agent))
                            {
                                agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                publicAgentActions.Add(act.agent, new List<Action>());
                                publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                            }
                            break;
                        }
                    }

                }
                if (act.agent == null)
                {
                    fail++;
                }
                else
                {
                    if (!agentActions.ContainsKey(act.agent))
                    {
                        agentActions.Add(act.agent, new List<Action>());
                        agentActions[act.agent].Add(act);
                    }
                    else
                    {
                        agentActions[act.agent].Add(act);
                    }

                    foreach (GroundedPredicate gp in act.HashPrecondition)
                    {
                        if (!agentPredicate[act.agent].Contains(gp))
                        {
                            agentPredicate[act.agent].Add(gp);
                        }
                    }
                    foreach (GroundedPredicate gp in act.HashEffects)
                    {
                        if (!agentPredicate[act.agent].Contains(gp))
                        {
                            agentPredicate[act.agent].Add(gp);
                        }

                        if (!agentEffPredicate.ContainsKey(gp))
                        {
                            agentEffPredicate.Add(gp, new List<string>());
                            agentEffPredicate[gp].Add(act.agent);
                        }
                        else
                        {
                            if (!agentEffPredicate[gp].Contains(act.agent))
                                agentEffPredicate[gp].Add(act.agent);
                        }
                    }
                }
            }

            foreach (Action dellAct in dell)
            {
                actions.Remove(dellAct);
            }

        }
        public void FindPublicAndPrivateAction(out List<Action> publicAction, out List<Action> privateAction)
        {
            publicAction = new List<Action>();
            privateAction = new List<Action>();
            agentActionl = new Dictionary<string, List<Action>>();
            foreach (Action act in groundedAction)
            {
                if (!agentActionl.ContainsKey(act.agent))
                {
                    agentActionl.Add(act.agent, new List<Action>());
                    agentActionl[act.agent].Add(act);
                }
                else
                    agentActionl[act.agent].Add(act);
            }
            numberOfAgent = agentActionl.Count;
            //agentActions = agentActionl;
            foreach (var pair in agentActionl)
            {
                foreach (Action act1 in pair.Value)
                {

                    foreach (var pair2 in agentActionl)
                    {
                        if (pair2.Key != pair.Key)
                        {
                            foreach (Action act2 in pair2.Value)
                            {
                                bool publicFlag = false;
                                foreach (GroundedPredicate eff in act1.HashEffects)
                                {
                                    if (act2.HashPrecondition.Contains(eff))
                                    {
                                        publicFlag = true;
                                        if (!publicAgentPredicate.ContainsKey(act1.agent))
                                        {
                                            publicAgentPredicate.Add(act1.agent, new HashSet<GroundedPredicate>());
                                            publicAgentPredicate[act1.agent].Add(eff);
                                            
                                        }
                                        else
                                        {
                                            if (!publicAgentPredicate[act1.agent].Contains(eff))
                                                publicAgentPredicate[act1.agent].Add(eff);
                                           
                                        }
                                        if (!publicAgentPredicate.ContainsKey(act2.agent))
                                        {
                                            publicAgentPredicate.Add(act2.agent, new HashSet<GroundedPredicate>());
                                            publicAgentPredicate[act2.agent].Add(eff);

                                        }
                                        else
                                        {
                                            if (!publicAgentPredicate[act2.agent].Contains(eff))
                                                publicAgentPredicate[act2.agent].Add(eff);
                                        }
                                       // continue;
                                    }
                                }
                                if (!publicFlag)
                                {
                                    foreach (GroundedPredicate eff in act1.HashEffects)
                                    {
                                        if (act2.HashEffects.Contains(eff))
                                        {
                                            publicFlag = true;
                                            if (!publicAgentPredicate.ContainsKey(act1.agent))
                                            {
                                                publicAgentPredicate.Add(act1.agent, new HashSet<GroundedPredicate>());
                                                publicAgentPredicate[act1.agent].Add(eff);

                                            }
                                            else
                                            {
                                                if (!publicAgentPredicate[act1.agent].Contains(eff))
                                                    publicAgentPredicate[act1.agent].Add(eff);

                                            }
                                            if (!publicAgentPredicate.ContainsKey(act2.agent))
                                            {
                                                publicAgentPredicate.Add(act2.agent, new HashSet<GroundedPredicate>());
                                                publicAgentPredicate[act2.agent].Add(eff);

                                            }
                                            else
                                            {
                                                if (!publicAgentPredicate[act2.agent].Contains(eff))
                                                    publicAgentPredicate[act2.agent].Add(eff);
                                            }
                                            // continue;
                                        }
                                    }
                                }
                                if (publicFlag)
                                {
                                    if (!publicAgentActions.ContainsKey(act1.agent))
                                    {
                                        publicAgentActions.Add(act1.agent, new List<Action>());
                                        publicAgentActions[act1.agent].Add(act1);
                                    }
                                    else
                                    {
                                        if (!publicAgentActions[act1.agent].Contains(act1))
                                        {
                                            publicAgentActions[act1.agent].Add(act1);
                                        }
                                    }

                                    if (!publicAgentActions.ContainsKey(act2.agent))
                                    {
                                        publicAgentActions.Add(act2.agent, new List<Action>());
                                        publicAgentActions[act2.agent].Add(act2);
                                    }
                                    else
                                    {
                                        if (!publicAgentActions[act2.agent].Contains(act2))
                                        {
                                            publicAgentActions[act2.agent].Add(act2);
                                        }
                                    }


                                    if (!publicAction.Contains(act1))
                                        publicAction.Add(act1);
                                    if (!publicAction.Contains(act2))
                                        publicAction.Add(act2);
                                }
                            }
                        }
                    }
                }
            }


            foreach (Action act in groundedAction)
            {
                if (!publicAction.Contains(act))
                {
                    privateAction.Add(act);

                    if (!privateAgentActions.ContainsKey(act.agent))
                    {
                        privateAgentActions.Add(act.agent, new List<Action>());
                        privateAgentActions[act.agent].Add(act);
                    }
                    else
                    {
                        if (!privateAgentActions[act.agent].Contains(act))
                        {
                            privateAgentActions[act.agent].Add(act);
                        }
                    }
                }
            }

        }
        public List<Action> getProjectionPublicActionForAgent(string agent)
        {
            List<Action> allPublicActions = new List<Action>();
            HashSet<Predicate> allPublicPredicate = new HashSet<Predicate>();
            HashSet<Predicate> allPublicPredicateWithMyPrivate = new HashSet<Predicate>();
            foreach (var name in publicAgentPredicate.Keys)
            {


                foreach (GroundedPredicate gp in publicAgentPredicate[name])
                {
                    if (!allPublicPredicate.Contains(gp))
                        allPublicPredicate.Add(gp);

                    if (!allPublicPredicateWithMyPrivate.Contains(gp))
                        allPublicPredicateWithMyPrivate.Add(gp);
                }

                if (name.Equals(agent))
                {
                    foreach (GroundedPredicate gp in publicAgentPredicate[name])
                    {


                        foreach (GroundedPredicate gp2 in agentPredicate[name])
                        {
                            if (!allPublicPredicateWithMyPrivate.Contains(gp2))
                                allPublicPredicateWithMyPrivate.Add(gp2);
                        }
                    }
                }

            }


            foreach (var name in publicAgentPredicate.Keys)
            {
                if (!name.Equals(agent))
                {
                    foreach (Action act in publicAgentActions[name])
                    {
                        Action newAct = new Action(act.Name);
                        CompoundFormula effect = new CompoundFormula("and");
                        CompoundFormula preCond = new CompoundFormula("and");
                        foreach (GroundedPredicate eff in act.HashEffects)
                        {
                            if (allPublicPredicateWithMyPrivate.Contains(eff) || allPublicPredicateWithMyPrivate.Contains(eff.Negate()))
                                effect.AddOperand(eff);
                        }
                        foreach (GroundedPredicate pre in act.HashPrecondition)
                        {
                            if (allPublicPredicate.Contains(pre) || allPublicPredicate.Contains(pre.Negate()))
                                preCond.AddOperand(pre);
                        }

                        newAct.Effects = effect;
                        newAct.Preconditions = preCond;
                        newAct.LoadPrecondition();
                        allPublicActions.Add(newAct);
                    }
                }


            }

            return allPublicActions;
        }
        
    }
}
