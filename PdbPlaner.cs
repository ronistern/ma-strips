using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class PdbPlaner
    {
        List<Agent> agents = null;
        Domain d;
        Problem p;
        int countOfLandmarks = 0;
        List<Action> publicActions = null;
        PatternDatabase pd = null;
        Dictionary<string, HashSet<CompoundFormula>> agentEffect = new Dictionary<string, HashSet<CompoundFormula>>();
        // StreamWriter sw = new StreamWriter("sss.txt", false);
        public PdbPlaner(List<Agent> m_agents, List<Landmark> goals, PatternDatabase pd)
        {
           // d = m_d;
           // p = m_p;
            agents = m_agents;
            this.pd = pd;
            publicActions = new List<Action>();

            foreach (Agent agent in agents)
            {

                agentEffect.Add(agent.name, new HashSet<CompoundFormula>());
                foreach (Action act in agent.publicActions)
                {
                    CompoundFormula eff = new CompoundFormula("and");
                    foreach (GroundedPredicate gp in act.HashEffects)
                    {
                        if (agent.PublicPredicates.Contains(gp))
                        {
                            eff.AddOperand(gp);
                        }

                    }
                    if (!agentEffect[agent.name].Contains(eff))
                    {
                        agentEffect[agent.name].Add(eff);
                    }
                }
                agent.initPdbPlaner();
                countOfLandmarks += agent.GetNumberOfRestLandmarks();

            }
            PdbVertex.initVertxClass(agents, d, p, goals, pd);

        }


        private bool CheckAgentEquality()
        {
            List<HashSet<Predicate>> lAgentsEffects = new List<HashSet<Predicate>>();
            foreach (Agent a in agents)
            {
                HashSet<Predicate> lAllSingleAgentPublicEffects = new HashSet<Predicate>();
                foreach (Action aAction in a.publicActions)
                {
                    HashSet<Predicate> lEffects = aAction.GetMandatoryEffects();
                    foreach (GroundedPredicate p in lEffects)
                        if (!p.Negation && a.PublicPredicates.Contains(p))
                            lAllSingleAgentPublicEffects.Add(p);
                }
                if (lAgentsEffects.Count > 0)
                {
                    if (lAgentsEffects[0].Count != lAllSingleAgentPublicEffects.Count)
                        return false;
                    foreach (Predicate p in lAllSingleAgentPublicEffects)
                        if (!lAgentsEffects[0].Contains(p))
                            return false;

                }
                lAgentsEffects.Add(lAllSingleAgentPublicEffects);
            }
            return true;
        }
     

        public List<string> Plan()
        {
            bool bAllAgentsEqual = CheckAgentEquality();

            int i = 300;// countOfLandmarks;
            int[] statesNum = new int[agents.Count];
            for (int k = 0; k < statesNum.Length; k++)
            {
                statesNum[k] = 0;
            }


            PdbVertex rootVertex = new PdbVertex(statesNum, new List<Action>(), 0, 0, 0, null, null);
            rootVertex.publicState = new State((Problem)null);
            foreach(Agent agent in agents)
            {
                foreach (GroundedPredicate pgp in agent.GetPublicInitial())
                {
                    if (!rootVertex.publicState.Contains(pgp))
                    {
                        rootVertex.publicState.AddPredicate(pgp);
                    }
                }
            }
            //DateTime begin = DateTime.Now;

            int count = 0;
            PdbVertex curentVertex = null;
            DateTime dtStart = DateTime.Now;
            //for (; i < 1000; i++)
            {
                HashSet<int[]> lVisited = new HashSet<int[]>(new ComparerArray());
                HashSet<PdbVertex> lVisited2 = new HashSet<PdbVertex>();
                DateTime begin = DateTime.Now;
                List<PdbVertex> queue = new List<PdbVertex>();
                //PriorityQueue<PdbVertex, double> queue2 = new PriorityQueue<PdbVertex, double>(PdbVertex.ComparerDouble);
                //PriorityQueue<PdbVertex, double> queue2 = new PriorityQueue<PdbVertex, double>();
                //Heap heap = new Heap(1000000);
                //queue2.Insert(rootVertex, rootVertex.h);
                //heap.Insert(rootVertex);
                queue.Add(rootVertex);
                lVisited.Add(rootVertex.statesNubmber);
                // double priority = -1 * (rootVertex.h + (double)(rootVertex.g) / 100000 );

                //queue2.Enqueue(rootVertex, priority);
                int temp = 0;
                List<string> lplan = null;// new List<string>();
                bool flag = true;
                int c = 0;
                double minh = 99999999;
                while (queue.Count > 0)
                {
                    c++;
                    if (c % 1000 == 0)
                    {
                        //Console.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\bExpanded: " + c + ", open: " + queue.Count + ", h: " + curentVertex.h + ", T: " + (int)(DateTime.Now - dtStart).TotalSeconds);
                        Console.Write("\rExpanded: " + c + ", open: " + queue.Count + ", h: " + curentVertex.h + ", T: " + (int)(DateTime.Now - dtStart).TotalSeconds);
                        if (queue.Count > 200000)
                        {
                            return null;
                            Console.WriteLine();
                            Console.WriteLine("Queue too large, breaking.");
                        }
                    }
                    flag = true;
                    //curentVertex = queue[0];
                    // List<PriorityQueueItem<PdbVertex,double>> v = queue2.ToList();
                    //curentVertex = queue2.Dequeue().Value;
                    temp++;
                    curentVertex = FindMin(queue);// queue[0];// heap.Remove();
                    // queue.Remove(curentVertex);
                    // queue.RemoveAt(0);
                    count++;
                    bool bDeadend = curentVertex.IsDeadEnd();
                    if (bDeadend)
                        continue;
                    

                    //                    if (curentVertex.Parent != null && curentVertex.Parent.Parent != null && curentVertex.h == curentVertex.Parent.h && curentVertex.h == curentVertex.Parent.Parent.h)
                    //                        Console.WriteLine("stuck!");

                   

                    // Program.messages += agents.Count;
                    int f = 0;
                    List<PdbVertex> needUpDate = new List<PdbVertex>();
                    HashSet<CompoundFormula> levelPotential = new HashSet<CompoundFormula>();
                    int index = 1;
                    bool con = false;
                    if (curentVertex.h == 0)
                    {
                        curentVertex.publicPredicateImplications = new List<HashSet<CompoundFormula>>();
                        PdbVertex tmp = curentVertex;
                        while (tmp != null)
                        {
                            curentVertex.publicPredicateImplications.Insert(0, tmp.canGetInParallel);
                            tmp = tmp.Parent;
                        }
                        string isGoal = curentVertex.IsGoal(out lplan);
                        if (isGoal.Equals("true"))
                        {
                            double time = ((double)((DateTime.Now.Subtract(begin)).Minutes)) * 60.0;
                            time += ((double)((DateTime.Now.Subtract(begin)).Seconds));
                            time += ((double)((DateTime.Now.Subtract(begin)).Milliseconds) / 1000);
                            //Console.WriteLine(time);
                            //Console.WriteLine(lplan.Count);
                            // Console.WriteLine(((double)((DateTime.Now.Subtract(begin)).Milliseconds) / 1000));
                            Program.times.Add(time);
                            Program.countActions.Add(lplan.Count);
                            Program.timeSum += time;
                            Program.actionSum += lplan.Count;

                            /* foreach (Action act in curentVertex.lplan)
                             {
                                 sw.WriteLine(act.Name);
                                 lplan.Add(act.Name);
                             }
                             sw.Close();*/
                            return lplan;
                        }
                        if (!isGoal.Equals("false"))
                        {
                            //return null;
                        }
                    }

                    bool stop = false;
                    foreach (Agent agent in agents)
                    {
                        foreach (Action act in agent.publicActions)
                        {
                            f++;
                            Program.messages += agents.Count;
                            PdbVertex newVertex = curentVertex.Apply(agent.name, act);

                            bool bVisited = true;
                            if (newVertex != null)
                            {
                                if (bAllAgentsEqual)
                                    bVisited = lVisited2.Contains(newVertex);
                                else
                                    bVisited = lVisited.Contains(newVertex.statesNubmber);
                            }
                            if (!bVisited)
                            {
                            

                               // newVertex.History = new List<string>(curentVertex.History);
                               // newVertex.History.Add(act.Name);

                               // newVertex.g += (double)index / 1000000;
                                queue.Add(newVertex);
                              
                                if (minh > newVertex.h)
                                {
                                    minh = newVertex.h;
                                  //  if(minh==0)
                                        Console.WriteLine(minh);
                                      //  break;
                                }
                                if (newVertex.h < curentVertex.h)
                                {
                                    stop = true;
                                    break;
                                }
                                index++;
                               
                                //queue2.Enqueue(newVertex, priority);
                                // needUpDate.Add(newVertex);
                                 CompoundFormula effect = new CompoundFormula("and");
                                 foreach (GroundedPredicate gp in act.HashEffects)
                                 {
                                     if (agent.PublicPredicates.Contains(gp))
                                         effect.AddOperand(gp);
                                 }
                                 levelPotential.Add(effect);

                              
                            }

                        }
                        if (stop)
                            break;

                    }
                    curentVertex.canGetInParallel = levelPotential;                                      
                }
            }
            return null;
        }

        public PdbVertex FindMin(List<PdbVertex> lvertxs)
        {
            int index = 0;
            int counter = 0;
            PdbVertex min = lvertxs.ElementAt(0);
            foreach (PdbVertex v in lvertxs)
            {
                if (PdbVertex.Comparer(min, v) == 1)
                {
                    min = v;
                    index = counter;
                }
                counter++;
            }

            var ans = lvertxs.ElementAt(index);
            lvertxs.RemoveAt(index);
            return ans;
        }
    }
}
