using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace Planning
{
    class BuildAgents_II
    {
        Problem problem = null;
        Domain domain = null;

        public Dictionary<string, HashSet<GroundedPredicate>> agentPredicate = new Dictionary<string, HashSet<GroundedPredicate>>();
        public Dictionary<GroundedPredicate, List<string>> agentEffPredicate = new Dictionary<GroundedPredicate, List<string>>();
        public Dictionary<string, HashSet<GroundedPredicate>> agentEff = new Dictionary<string, HashSet<GroundedPredicate>>();
        public Dictionary<string, HashSet<GroundedPredicate>> publicAgentPredicate = new Dictionary<string, HashSet<GroundedPredicate>>();
        List<Action> groundedAction = new List<Action>();
        private Dictionary<string, List<Action>> agentActions = new Dictionary<string, List<Action>>();
        private Dictionary<string, List<Action>> publicAgentActions = new Dictionary<string, List<Action>>();
        private Dictionary<string, List<Action>> privateAgentActions = new Dictionary<string, List<Action>>();
        public List<Action> publicAction = null;
        public List<Action> privateAction = null;
        public static Dictionary<string, HashSet<string>> mapActionNameToAgents = null;
        Dictionary<string, List<Action>> agentActionl;
        int numberOfAgent = -1;
        Dictionary<Predicate, List<string>> sharePublicPredicate = new Dictionary<Predicate, List<string>>();
        Dictionary<Predicate, List<string>> canGetPublicPredicate = new Dictionary<Predicate, List<string>>();
        Dictionary<string, State> agentsStartState = new Dictionary<string, State>();
        Dictionary<string, List<GroundedPredicate>> agentsGoal = new Dictionary<string, List<GroundedPredicate>>();
        List<Agent> agents = new List<Agent>();
        public BuildAgents_II(Problem p, Domain d, string folderName, string domainName, string problemName)
        {
            problem = p;
            domain = d;
            groundedAction = domain.GroundAllActions(p);
            DivideActions(groundedAction, folderName);
            FindPublicAndPrivateAction(out publicAction, out privateAction);
            FindPublicPredicate();
            DivideStartState();
            DivideGoal();
            Dictionary<Predicate, HashSet<Predicate>> lInvariants = null;
            if (folderName.Contains("MABlocksWorld") || folderName.Contains("cMABlocks"))
            {
                lInvariants = d.IdentifyInvariants(d.groundedAction);
            }
            else
            {
                try
                {
                    //lInvariants = d.IdentifyMutexSAS(folderName, domainName, problemName);
                }
                catch (Exception ex)
                {
                    // lInvariants = new Dictionary<Predicate, HashSet<Predicate>>();
                }
            }

            foreach (var agentName in agentPredicate.Keys)
            {
                if (!agentsGoal.ContainsKey(agentName))
                {
                    agentsGoal.Add(agentName, new List<GroundedPredicate>());
                }
                Agent agent = new Agent(p, d, agentActions[agentName], publicAgentActions[agentName], privateAgentActions[agentName], agentPredicate[agentName], publicAgentPredicate[agentName], agentsStartState[agentName], agentsGoal[agentName], agentName, getProjectionPublicActionForAgent(agentName), lInvariants);
                agents.Add(agent);
            }
        }
        public BuildAgents_II(List<Domain> lNotGroundedDomains, List<Domain> domains, List<Problem> problems)
        {
            HashSet<Predicate> lAllGoals = new HashSet<Predicate>();
            HashSet<Predicate> lAllDividedGoals = new HashSet<Predicate>();
            HashSet<Constant> publicConst = new HashSet<Constant>();
            for (int i = 0; i < domains.Count; i++)
            {
                foreach (Constant cons in domains.ElementAt(i).PublicConstants)
                {
                    publicConst.Add(cons);
                }
            }
            for (int i = 0; i < domains.Count; i++)
            {

                Problem p = problems.ElementAt(i);
                Domain d = domains.ElementAt(i);
                Domain notGroundedDomain = lNotGroundedDomains.ElementAt(i);
                foreach (Constant cons in publicConst)
                {
                    if (!notGroundedDomain.Constants.Contains(cons))
                    {
                        notGroundedDomain.Constants.Add(cons);
                    }
                }
                Dictionary<Predicate, HashSet<Predicate>> lInvariants = null;
                //lInvariants = new Dictionary<Predicate,HashSet<Predicate>>();

                HashSet<GroundedPredicate> publicPredicates = new HashSet<GroundedPredicate>();
                HashSet<GroundedPredicate> Predicates = new HashSet<GroundedPredicate>();
                d.Predicates = new HashSet<Predicate>();
                foreach (GroundedPredicate gp in d.PublicPredicates)
                {
                    publicPredicates.Add(gp);
                    Predicates.Add(gp);
                    GroundedPredicate ngp = (GroundedPredicate)gp.Negate();
                    publicPredicates.Add(ngp);
                    Predicates.Add(ngp);

                    d.Predicates.Add(gp);
                    d.Predicates.Add(ngp);
                }


                foreach (GroundedPredicate gp in d.PrivatePredicates)
                {
                    Predicates.Add(gp);
                    GroundedPredicate ngp = (GroundedPredicate)gp.Negate();
                    Predicates.Add(ngp);

                    d.Predicates.Add(gp);
                    d.Predicates.Add(ngp);
                }

                State initialState = new State(p);
                /*foreach(GroundedPredicate gp in p.Known)
                {                   
                     initialState.AddPredicate(gp);
                }*/
                foreach (Predicate gp in p.Known)
                {
                    if (gp is GroundedPredicate)
                        initialState.AddPredicate(gp);
                }
                d.groundedAction = d.Actions;

                List<GroundedPredicate> goal = DivideGoal(p.Goal, d.PublicActions.ToList(), d.PrivateActions.ToList(), publicPredicates);
                lAllGoals.UnionWith(p.Goal.GetAllPredicates());
                foreach (Predicate pGoal in goal)
                    lAllDividedGoals.Add(pGoal);

                BuildTables(domains);
                List<Action> projPublicActions = getProjectionPublicActionForAgent("Agent: " + i.ToString());
                notGroundedDomain.Actions = new List<Action>(d.Actions);
                notGroundedDomain.Actions.AddRange(projPublicActions);
                /* bool f = true;
                 while (f)
                 {
                     f = false;
                     foreach (Action act in projPublicActions)
                     {
                         bool preInclude = true;
                         foreach(GroundedPredicate gp in act.HashPrecondition)
                         {
                             if (!initialState.Contains(gp))
                             {
                                 preInclude = false;
                                 break;
                             }
                         }
                         if (preInclude)
                         {
                             foreach (GroundedPredicate gp in act.HashEffects)
                             {
                                 if (!gp.Negation && !initialState.Contains(gp))
                                 {
                                     initialState.AddPredicate(gp);
                                     f = true;
                                 }
                             }
                         }
                     }
                 }*/
                //lInvariants = notGroundedDomain.IdentifyMutexSAS(p, initialState);

                //lInvariants = new Dictionary<Predicate, HashSet<Predicate>>();
                projPublicActions.AddRange(d.groundedAction);
                lInvariants = d.IdentifyStrongInvariants(projPublicActions);
                Dictionary<Predicate, HashSet<Predicate>> tmp = d.IdentifyInvariants(projPublicActions);
                foreach (var kv in tmp)
                {
                    if (!lInvariants.ContainsKey(kv.Key))
                    {
                        lInvariants.Add(kv.Key, kv.Value);
                    }
                    else
                    {
                        foreach (GroundedPredicate gp in kv.Value)
                        {
                            lInvariants[kv.Key].Add(gp);
                        }
                    }
                }
                foreach (Action act in d.groundedAction)
                {
                    if (!mapActionNameToAgents.ContainsKey(act.Name))
                        mapActionNameToAgents.Add(act.Name, new HashSet<string>());
                    mapActionNameToAgents[act.Name].Add("Agent: " + i.ToString());
                }
                Agent agent = new Agent(p, notGroundedDomain, d.groundedAction, d.PublicActions.ToList(), d.PrivateActions.ToList(), Predicates, publicPredicates, initialState, goal, "Agent: " + i.ToString(), projPublicActions, lInvariants);
                agents.Add(agent);
            }
            //There is a problem with goals that are satisfied in the initial state and are constant - not handling for now
            //if (!lAllDividedGoals.Equals(lAllGoals))
            //    throw new Exception("Some goals cannot be obtained by any agent");
        }

        public List<Agent> ReturnAgents()
        {
            return agents;
        }
        public List<Agent> CreateAgents()
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

                List<string> agents = null;
                if (agentEffPredicate.ContainsKey(gp))
                    agents = agentEffPredicate[gp];
                else
                    agents = new List<string>();
                foreach (var pair in agentsStartState)
                {
                    if (pair.Value.Contains(gp))
                    {
                        if (!agents.Contains(pair.Key))
                        {
                            agents.Add(pair.Key);
                        }
                    }
                }

                bool publicGoal = false;
                if (agents.Count > 1)
                {
                    publicGoal = true;
                    //  throw new NotImplementedException();
                }
                if (publicGoal)
                {
                    gp.isPublic = true;
                }
                foreach (string agent in agents)
                {
                    if (!agentsGoal.ContainsKey(agent))
                    {
                        agentsGoal.Add(agent, new List<GroundedPredicate>());
                        agentsGoal[agent].Add(gp);
                    }
                    else
                    {
                        agentsGoal[agent].Add(gp);
                    }
                }
            }

        }
        private List<GroundedPredicate> DivideGoal(Formula goal, List<Action> publicActions, List<Action> privateActions, HashSet<GroundedPredicate> publicFacts)
        {
            List<GroundedPredicate> localGoal = new List<GroundedPredicate>();
            //agentsStartState.Add(pair.Key, new List<GroundedPredicate>());

            foreach (GroundedPredicate gp in goal.GetAllPredicates())
            {
                bool flag = false;
                foreach (Action act in publicActions)
                {
                    if (act.Effects.GetAllPredicates().Contains(gp))
                    {
                        // gp.isPublic = true;
                        flag = true;
                        localGoal.Add(gp);
                        break;
                    }
                    if (act.Preconditions.GetAllPredicates().Contains(gp))
                    {
                        //gp.isPublic = true;
                        flag = true;
                        localGoal.Add(gp);
                        break;
                    }
                }
                if (flag != true)
                {
                    foreach (Action act in privateActions)
                    {
                        if (act.Effects.GetAllPredicates().Contains(gp))
                        {
                            flag = true;
                            localGoal.Add(gp);
                            break;
                        }
                    }
                }
                if (flag)
                {
                    if (publicFacts.Contains(gp))
                    {
                        gp.isPublic = true;
                    }
                }
            }
            return localGoal;

        }
        private void DivideActions(List<Action> actions, string par)
        {
            agentPredicate = new Dictionary<string, HashSet<GroundedPredicate>>();
            agentEff = new Dictionary<string, HashSet<GroundedPredicate>>();
            List<Action> dell = new List<Action>();
            int fail = 0;

            foreach (Action act in actions)
            {
                bool con1 = false;

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
                        if (par.Contains("Logistics") || par.Contains("tmp"))
                        {
                            f = arg.Name.Contains("tru");
                        }
                        if ((arg.Name.Contains("rover") && arg.Name.Length == 6) || arg.Name.Contains("fast") || arg.Name.Contains("slow") || arg.Name.Contains("plane") || arg.Name.Contains("apn") || arg.Name.Contains("satellite") || arg.Name.Contains("aircraft") || f)// || arg.Name.Contains("tru"))
                        {
                            act.agent = arg.Name;
                            if (!agentPredicate.ContainsKey(act.agent))
                            {
                                agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                publicAgentActions.Add(act.agent, new List<Action>());
                                publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                privateAgentActions.Add(act.agent, new List<Action>());

                            }
                            if (!agentEff.ContainsKey(act.agent))
                            {
                                agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                            }
                            con1 = true;
                            break;
                        }
                        if (con1)
                            break;
                        if (par.Contains("MABlocksWorld") || par.Contains("cMABlocks"))
                        {
                            if (act.Name.Contains("a0"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a0";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;
                            if (act.Name.Contains("a1"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a1";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;
                            if (act.Name.Contains("a2"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a2";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;
                            if (act.Name.Contains("a3"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a3";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;
                            if (act.Name.Contains("a4"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a4";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;

                            if (act.Name.Contains("a5"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a5";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;
                            if (act.Name.Contains("a6"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a6";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;
                            if (act.Name.Contains("a7"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a7";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;
                            if (act.Name.Contains("a8"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a8";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;
                            if (act.Name.Contains("a9"))// || arg.Name.Contains("tru"))
                            {
                                act.agent = "a9";
                                if (!agentPredicate.ContainsKey(act.agent))
                                {
                                    agentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    publicAgentActions.Add(act.agent, new List<Action>());
                                    publicAgentPredicate.Add(act.agent, new HashSet<GroundedPredicate>());
                                    privateAgentActions.Add(act.agent, new List<Action>());
                                }
                                if (!agentEff.ContainsKey(act.agent))
                                {
                                    agentEff.Add(act.agent, new HashSet<GroundedPredicate>());
                                }
                                con1 = true;
                                break;
                            }
                            if (con1)
                                break;

                        }
                    }
                    if (con1)
                        break;
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

                        if (!agentEff[act.agent].Contains(gp))
                        {
                            agentEff[act.agent].Add(gp);
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




            foreach (Action act in groundedAction)
            {
                bool isPublic = false;

                foreach (var agentsPredicate in agentEff)
                {
                    if (agentsPredicate.Key.Equals(act.agent))
                    {
                        continue;
                    }
                    foreach (GroundedPredicate eff in act.HashEffects)
                    {
                        if (agentsPredicate.Value.Contains(eff))
                        {
                            publicAction.Add(act);
                            publicAgentActions[act.agent].Add(act);
                            isPublic = true;
                            break;
                        }
                    }
                    if (isPublic)
                        break;

                    foreach (GroundedPredicate pre in act.HashPrecondition)
                    {
                        if (agentsPredicate.Value.Contains(pre))
                        {
                            publicAction.Add(act);
                            publicAgentActions[act.agent].Add(act);
                            isPublic = true;
                            break;
                        }
                    }
                    if (isPublic)
                        break;

                }
                if (!isPublic)
                {
                    privateAction.Add(act);
                    privateAgentActions[act.agent].Add(act);
                }
            }
        }

        private void FindPublicPredicate()
        {
            foreach (var agentsPredicate in agentPredicate)
            {
                foreach (GroundedPredicate gp in agentsPredicate.Value)
                {

                    foreach (var ap in agentPredicate)
                    {
                        if (ap.Key.Equals(agentsPredicate.Key))
                            continue;

                        if (ap.Value.Contains(gp))
                        {

                            publicAgentPredicate[agentsPredicate.Key].Add(gp);
                            break;
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

                /*if (name.Equals(agent))
                {



                        foreach (GroundedPredicate gp2 in agentPredicate[name])
                        {
                            if (!allPublicPredicateWithMyPrivate.Contains(gp2))
                                allPublicPredicateWithMyPrivate.Add(gp2);
                        }

                }*/

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
                            if (allPublicPredicate.Contains(eff) || allPublicPredicate.Contains(eff.Negate()))
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

        public void BuildTables(List<Domain> lDomains)
        {
            publicAgentPredicate = new Dictionary<string, HashSet<GroundedPredicate>>();
            publicAgentActions = new Dictionary<string, List<Action>>();
            for (int i = 0; i < lDomains.Count; i++)
            {

                publicAgentPredicate.Add("Agent: " + i.ToString(), new HashSet<GroundedPredicate>(lDomains.ElementAt(i).PublicPredicates.Cast<GroundedPredicate>()));
                publicAgentActions.Add("Agent: " + i.ToString(), lDomains.ElementAt(i).PublicActions.ToList());
            }
        }

    }
}
