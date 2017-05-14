using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;

namespace Planning
{
    class PatternDatabase
    {

        private static string[] PDB_FACT_NAMES = new string[] { "on", "at", "passenger-at", "has-data", "is-message-at", "treatment", "surface-condition", "colour" };

        public Dictionary<GroundedPredicate, Dictionary<GroundedPredicate, int>> cooperationCanGet = null;
        public static List<string> ffLplan = null;
        public PatternDatabase(List<Domain> domains, List<Problem> problems, List<Agent> agents,string path)
        {
            try
            {
                Console.WriteLine("Computing PDB");
                if (File.Exists(path))
                {
                    cooperationCanGet = new Dictionary<GroundedPredicate, Dictionary<GroundedPredicate, int>>();
                    Dictionary<string, GroundedPredicate> mapStringtoPublicPredicate = new Dictionary<string, GroundedPredicate>();
                    foreach (Agent agent in agents)
                    {
                        foreach (GroundedPredicate publicGp in agent.PublicPredicates)
                        {
                            if (!mapStringtoPublicPredicate.ContainsKey(publicGp.ToString()))
                            {
                                mapStringtoPublicPredicate.Add(publicGp.ToString(), publicGp);
                            }
                        }
                    }
                    StreamReader pdbReader = new StreamReader(path);
                    while (!pdbReader.EndOfStream)
                    {
                        string line = pdbReader.ReadLine();
                        string[] items = line.Split('~');
                        if(!mapStringtoPublicPredicate.ContainsKey(items[0]))
                            continue;
                        cooperationCanGet.Add(mapStringtoPublicPredicate[items[0]], new Dictionary<GroundedPredicate, int>());
                        for (int i = 1; i < items.Length; i++)
                        {
                            string[] targetCost = items[i].Split('&');
                            cooperationCanGet[mapStringtoPublicPredicate[items[0]]].Add(mapStringtoPublicPredicate[targetCost[0]], int.Parse(targetCost[1]));

                        }
                    }
                }
                else
                {
                    DateTime startTime = DateTime.Now;
                    int privateActionsCount = 0;
                    foreach (Agent ag in agents)
                    {
                        privateActionsCount += ag.privateActions.Count;
                    }




                    Dictionary<GroundedPredicate, Dictionary<GroundedPredicate, int>> canGet = null;
                    List<Dictionary<GroundedPredicate, Dictionary<GroundedPredicate, int>>> agentCanGet = new List<Dictionary<GroundedPredicate, Dictionary<GroundedPredicate, int>>>();
                    HSPHeuristic hsp = null;
                    ForwardSearchPlanner forwardSearch = null;
                    HashSet<GroundedPredicate> publicPredicates = null;
                    int i = 0;
                    cooperationCanGet = new Dictionary<GroundedPredicate, Dictionary<GroundedPredicate, int>>();
                    foreach (Agent agent in agents)
                    {

                        canGet = new Dictionary<GroundedPredicate, Dictionary<GroundedPredicate, int>>();
                        publicPredicates = new HashSet<GroundedPredicate>();
                        foreach (GroundedPredicate publicPredicate in agent.PublicPredicates)
                        {
                            if (!cooperationCanGet.ContainsKey(publicPredicate))
                            {
                                cooperationCanGet.Add(publicPredicate, new Dictionary<GroundedPredicate, int>());
                                cooperationCanGet[publicPredicate].Add(publicPredicate, 0);
                            }
                            if (publicPredicate.Negation || agent.invariantPredicate.Contains(publicPredicate) || publicPredicate.ToString().Equals("") || ((publicPredicate.Constants.Count > 1) && publicPredicate.Constants[0].Equals(publicPredicate.Constants[1])))
                                continue;
                            if (PDB_FACT_NAMES.Contains(publicPredicate.Name))
                                publicPredicates.Add(publicPredicate);
                        }
                        int counter = 0;
                        foreach (GroundedPredicate publicPredicate in publicPredicates)
                        {
                            counter++;
                            Console.Write("\rAgent " + i + ": " + counter + "/" + publicPredicates.Count + "           ");
                            if (!agent.MutuallyExclusive.ContainsKey(publicPredicate))
                                continue;
                            Constant constant1 = publicPredicate.Constants[0];
                            State s = new State(problems.ElementAt(i));
                            s.AddPredicate(publicPredicate);
                            foreach (Action publicAction in agent.publicActions)
                            {
                                if (publicAction.HashPrecondition.Contains(publicPredicate))
                                {
                                    foreach (var p in publicAction.HashPrecondition)
                                    {
                                        s.AddPredicate(p);
                                    }
                                }
                            }
                            HashSet<GroundedPredicate> mutex = new HashSet<GroundedPredicate>();
                            foreach (GroundedPredicate p in s.m_lPredicates)
                            {
                                if (agent.MutuallyExclusive.ContainsKey(p))
                                {
                                    foreach (GroundedPredicate mutexPredicate in agent.MutuallyExclusive[p])
                                    {
                                        mutex.Add(mutexPredicate);
                                    }
                                }
                            }

                            foreach (var gp in agent.Predicates)
                            {
                                if (!gp.Negation && !publicPredicates.Contains(gp) && !mutex.Contains(gp))
                                {
                                    //  if (!gp.ToString().Contains("at tru"))
                                    {
                                        s.AddPredicate(gp);
                                    }
                                }
                            }
                            int count2 = 0;
                            List<GroundedPredicate> facts = new List<GroundedPredicate>();
                            /*  facts.Add(publicPredicate);
                              bool stop = false;
                              while (!stop)
                              {
                                  stop = true;
                                  List<GroundedPredicate> tmp = new List<GroundedPredicate>();
                                  foreach (GroundedPredicate mGp in facts)
                                  {
                                      foreach (GroundedPredicate fact2 in agent.MutuallyExclusive[mGp])
                                      {
                                          if (!facts.Contains(fact2))
                                          {
                                              tmp.Add(fact2);
                                              stop = false;
                                          }
                                      }

                                  }
                                  foreach (GroundedPredicate add in tmp)
                                  {
                                      facts.Add(add);
                                  }
                              }
                              */
                            bool mutexGoal;
                            foreach (GroundedPredicate goal in publicPredicates)
                            {
                                count2++;
                                mutexGoal = true;
                                if (!publicPredicate.Name.Equals(goal.Name) || !publicPredicate.Constants[0].Equals(goal.Constants[0]))
                                    continue;
                                /*if (privateActionsCount == 0)
                                {
                                    if (!goal.Equals(publicPredicate))
                                        continue;
                                }*/
                                Constant constant2 = goal.Constants[0];
                                if (!agent.MutuallyExclusive[publicPredicate].Contains(goal) || !constant1.Equals(constant2))
                                {
                                    mutexGoal = false;
                                    //  if(!facts.Contains(goal))
                                    continue;
                                }
                                List<Predicate> localGoal = new List<Predicate>();
                                localGoal.Add(goal);
                                hsp = new HSPHeuristic(agent.m_actions, localGoal, false);
                                forwardSearch = new ForwardSearchPlanner(agent.m_actions, hsp);
                                List<Action> todo = forwardSearch.Plan(s, localGoal);
                                CompoundFormula goalCf = new CompoundFormula("and");
                               foreach (GroundedPredicate gp in localGoal)
                                    goalCf.AddOperand(gp);
                                bool isSolve;
                                ExternalPlanners externalPlanners = new ExternalPlanners();
                               // List<string> todo = externalPlanners.PdbFFPlan(domains.ElementAt(i), problems.ElementAt(i), s, goalCf, agent.m_actions, 5000, out isSolve);
                              //  List<string> todo = externalPlanners.Plan(true,true,domains.ElementAt(i), problems.ElementAt(i), s, goalCf, agent.m_actions, 5000, out isSolve);
                               // List<string> todo = externalPlanners.FFPlan(domains.ElementAt(i), problems.ElementAt(i), s, goalCf, agent.m_actions, 5000, out isSolve);
                               /* List<string> todo = new List<string>();
                                todo.Add("stump1");
                                todo.Add("stump2");
                                todo.Add("stump3");*/
                                if (todo != null)
                                {
                                    /* List<Action> actions = new List<Action>();
                                     bool insert = false;
                                     foreach (string actionName in todo)
                                     {
                                         Action act = agent.domain.mapActionNameToAction[actionName];
                                         actions.Add(act);
                                         if (act.Preconditions.GetAllPredicates().Contains(publicPredicate))
                                         {
                                             insert = true;
                                         }

                                     }*/
                                    //if (insert && (mutexGoal || todo.Count > 0))
                                    {
                                        if (!canGet.ContainsKey(publicPredicate))
                                        {
                                            canGet.Add(publicPredicate, new Dictionary<GroundedPredicate, int>());
                                        }
                                        canGet[publicPredicate].Add(goal, todo.Count);
                                        if (!mutexGoal & todo.Count > 0)
                                        {

                                            // Console.WriteLine(publicPredicate.ToString()+"   "+goal.ToString());
                                            //Program.messages3 += (agents.Count) * 2;
                                        }
                                    }
                                }

                            }
                            if (DateTime.Now.Subtract(startTime).TotalMinutes > 15)
                            {

                                WritePdb(path);
                                return;
                            }
                        }
                        agentCanGet.Add(canGet);
                        i++;
                    }


                    publicPredicates = new HashSet<GroundedPredicate>();
                    foreach (Agent agent in agents)
                    {

                        foreach (GroundedPredicate publicPredicate in agent.PublicPredicates)
                        {
                            if (publicPredicate.Negation || agent.invariantPredicate.Contains(publicPredicate) || publicPredicate.ToString().Equals("") || ((publicPredicate.Constants.Count > 1) && publicPredicate.Constants[0].Equals(publicPredicate.Constants[1])))
                                continue;
                            if (PDB_FACT_NAMES.Contains(publicPredicate.Name))
                                publicPredicates.Add(publicPredicate);
                        }
                    }
                    //cooperationCanGet = new Dictionary<GroundedPredicate, Dictionary<GroundedPredicate, int>>();
                    foreach (GroundedPredicate startPredicate in publicPredicates)
                    {
                        Dictionary<GroundedPredicate, int> openList = new Dictionary<GroundedPredicate, int>();
                        Dictionary<GroundedPredicate, int> closeList = new Dictionary<GroundedPredicate, int>();
                        openList.Add(startPredicate, 0);
                        while (openList.Count > 0)
                        {
                            KeyValuePair<GroundedPredicate, int> courentPredicate = openList.ElementAt(0);
                            openList.Remove(courentPredicate.Key);
                            closeList.Add(courentPredicate.Key, courentPredicate.Value);
                            int courentCost = courentPredicate.Value;
                            foreach (Dictionary<GroundedPredicate, Dictionary<GroundedPredicate, int>> canGetSet in agentCanGet)
                            {
                                if (!canGetSet.ContainsKey(courentPredicate.Key))
                                    continue;
                                foreach (KeyValuePair<GroundedPredicate, int> canGetPredicate in canGetSet[courentPredicate.Key])
                                {
                                    int addingCost = canGetPredicate.Value;
                                    if (openList.ContainsKey(canGetPredicate.Key))
                                    {
                                        if (openList[canGetPredicate.Key] > courentCost + addingCost)
                                            openList[canGetPredicate.Key] = courentCost + addingCost;
                                        continue;
                                    }
                                    if (closeList.ContainsKey(canGetPredicate.Key))
                                    {
                                        if (closeList[canGetPredicate.Key] > courentCost + addingCost)
                                        {
                                            closeList.Remove(canGetPredicate.Key);
                                            openList.Add(canGetPredicate.Key, courentCost + addingCost);
                                        }
                                        continue;
                                    }
                                    openList.Add(canGetPredicate.Key, courentCost + addingCost);


                                }
                            }
                        }
                        // cooperationCanGet.Add(startPredicate, new Dictionary<GroundedPredicate, int>());
                        foreach (KeyValuePair<GroundedPredicate, int> target in closeList)
                        {
                            if (!cooperationCanGet.ContainsKey(target.Key))
                            {
                                cooperationCanGet.Add(target.Key, new Dictionary<GroundedPredicate, int>());
                            }
                            if (!cooperationCanGet[target.Key].ContainsKey(startPredicate))
                                cooperationCanGet[target.Key].Add(startPredicate, target.Value);
                        }
                        //cooperationCanGet[startPredicate].Remove(startPredicate);

                    }

                    Program.messages2 += (agents.Count - 1) * agents.Count;
                    WritePdb(path);

                }
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.ToString());                    
            }
        }
        public void WritePdb(string path)
        {
            StreamWriter pdbWriter = new StreamWriter(path, false);
            foreach(var item in cooperationCanGet)
                {
                   
                    if(item.Value.Count>0)
                    {
                        pdbWriter.Write(item.Key.ToString()+"~");
                        int j = 0;
                        foreach(KeyValuePair<GroundedPredicate,int> targetCost in item.Value)
                        {
                            if (j == item.Value.Count - 1)
                            {
                                pdbWriter.Write(targetCost.Key.ToString() + "&" + targetCost.Value.ToString());
                            }
                            else
                            {
                                pdbWriter.Write(targetCost.Key.ToString() + "&" + targetCost.Value.ToString() + "~");
                            }
                            j++;
                        }
                        pdbWriter.WriteLine();
                    }
                }
                pdbWriter.Close();
        }
   }
}
