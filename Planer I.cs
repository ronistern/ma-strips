using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace Planning
{
    class Planer_I
    {
        List<Agent> agents = null;
        //Domain d;
       // Problem p;
        int countOfLandmarks = 0;
        bool first = true;
        List<Action> publicActions = null;
        public Planer_I(List<Agent> m_agents)
        {
           // d = m_d;
           // p = m_p;
            agents = m_agents;
            

            publicActions = new List<Action>();

            foreach (Agent agent in agents)
            {
                publicActions.AddRange(agent.publicActions);
                agent.initPlaner();
                countOfLandmarks += agent.GetNumberOfRestLandmarks();
                
            }
            Vertex.initVertxClass(agents);
            //countOfLandmarks = (countOfLandmarks / agents.Count) * 2;
           

        }

        public List<string> Plan()
        {

            bool bAllAgentsEqual = CheckAgentEquality();

            int i = 200;// countOfLandmarks;
            int[] statesNum = new int[agents.Count];
            for (int k = 0; k < statesNum.Length; k++)
            {
                statesNum[k] = 0;
            }


            Vertex rootVertex = new Vertex(statesNum, new List<Action>(), 0, countOfLandmarks, 0, null);

            //DateTime begin = DateTime.Now;

            int count = 0;
            Vertex curentVertex = null;
            DateTime dtStart = DateTime.Now;

            DateTime begin = DateTime.Now;
            List<Vertex> queue = new List<Vertex>();
            HashSet<int[]> lVisited = new HashSet<int[]>(new ComparerArray());
            HashSet<Vertex> lVisited2 = new HashSet<Vertex>();
            //PriorityQueue<Vertex, double> queue2 = new PriorityQueue<Vertex, double>(Vertex.ComparerDouble);
            //PriorityQueue<Vertex, double> queue2 = new PriorityQueue<Vertex, double>();
            //Heap heap = new Heap(1000000);
            //queue2.Insert(rootVertex, rootVertex.h);
            //heap.Insert(rootVertex);
            queue.Add(rootVertex);
            lVisited.Add(rootVertex.statesNubmber);
            lVisited2.Add(rootVertex);
            // double priority = -1 * (rootVertex.h + (double)(rootVertex.g) / 100000 );

            //queue2.Enqueue(rootVertex, priority);
            int temp = 0;
            List<string> lplan = null;// new List<string>();
            bool flag = true;
            int c = 0;
            int cResets = 0;
            double minh = 1000;
            int blindCounter = 0;
            TimeSpan tsDeadendDetection = new TimeSpan();
            while (queue.Count > 0)
            {
                c++;
                if (c % 30 == 0)
                {
                    //Console.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\bExpanded: " + c + ", open: " + queue.Count + ", h: " + curentVertex.h + ", T: " + (int)(DateTime.Now - dtStart).TotalSeconds);
                    Console.Write("\rExpanded: " + c + ", open: " + queue.Count +
                        ", h: " + curentVertex.h + ", h2: " + curentVertex.h2 + ", T: " + (int)(DateTime.Now - dtStart).TotalSeconds 
                        + ", deadend = " + (int)tsDeadendDetection.TotalSeconds);
                    if (queue.Count > 200000)
                    {
                        return null;
                        Console.WriteLine();
                        Console.WriteLine("Queue too large, breaking.");
                    }
                }
                flag = true;
                //curentVertex = queue[0];
                // List<PriorityQueueItem<Vertex,double>> v = queue2.ToList();
                //curentVertex = queue2.Dequeue().Value;
                temp++;
                curentVertex = FindMin(queue);// queue[0];// heap.Remove();
                // queue.Remove(curentVertex);
                DateTime dtBefore = DateTime.Now;
                bool bDeadend = curentVertex.IsDeadEnd();
                tsDeadendDetection += (DateTime.Now - dtBefore);
                if(bDeadend)
                    continue;
                // queue.RemoveAt(0);
                count++;
                if (false && curentVertex.BlindSearchDepth > 2)
                {
                    cResets++;
                    Vertex vLastImprovement = curentVertex;
                    while (vLastImprovement.Parent != null && vLastImprovement.Parent.h == curentVertex.h)
                        vLastImprovement = vLastImprovement.Parent;
                    int[] newStatesIndexs = new int[agents.Count];
                    int k = 0;
                   // List<State> lCurrentStartStates = new List<State>();
                    foreach (Agent agent in agents)
                    {
                     //   lCurrentStartStates.Add(agent.startState);
                        agent.ChangeInitialState(vLastImprovement.statesNubmber[k]);
                        k++;
                    }
                    Distributed_Landmarks_Detection.Landmarks_Detection(agents,false);
                  //  for (int j = 0; j < agents.Count; j++)
                   //     agents[j].startState = lCurrentStartStates[j];
                    k = 0;
                    foreach (Agent agent in agents)
                    {
                        newStatesIndexs[k] = agent.ResetStateInfo(vLastImprovement.statesNubmber[k]);
                        k++;
                    }

                    curentVertex = new Vertex(newStatesIndexs, new List<Action>(), 0, countOfLandmarks, 0, null);
                    curentVertex.History = vLastImprovement.History;
                    curentVertex.lplan = vLastImprovement.lplan;
                    minh = curentVertex.vectors.ElementAt(0)[0].Length;
                    queue = new List<Vertex>();
                    lVisited = new HashSet<int[]>();
                    lVisited.Add(curentVertex.statesNubmber);
                    lVisited2.Add(curentVertex);
                    blindCounter = 0;
                }
                blindCounter++;
                //                    if (curentVertex.Parent != null && curentVertex.Parent.Parent != null && curentVertex.h == curentVertex.Parent.h && curentVertex.h == curentVertex.Parent.Parent.h)
                //                        Console.WriteLine("stuck!");

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

                // Program.messages += agents.Count;
                int f = 0;
                List<Vertex> needUpDate = new List<Vertex>();
                HashSet<CompoundFormula> levelPotential = new HashSet<CompoundFormula>();
                int index = 1;
                bool con = false;
                List<Vertex> lExpanded = Expand(curentVertex,  levelPotential,needUpDate);
                foreach (Vertex newVertex in lExpanded)
                {
                    if (newVertex.actionNumber > 0)
                    {
                        f++;
                        queue.Add(newVertex);
                    }
                    f++;
                    newVertex.g += (double)index / 1000000;
                    bool bVisited = false;
                    if(bAllAgentsEqual)
                        bVisited = lVisited2.Contains(newVertex);
                    else
                        bVisited = lVisited.Contains(newVertex.statesNubmber);

                    if (!bVisited)
                    {
                        queue.Add(newVertex);
                        lVisited.Add(newVertex.statesNubmber);
                        lVisited2.Add(newVertex);
                    }
                    index++;
                    if (minh > newVertex.h)
                    {
                        minh = newVertex.h;
                        Console.WriteLine(minh);
                    }

                   /* if (Vertex.Comparer(newVertex, curentVertex) == -1 && !con)
                    {
                        blindCounter = 0;
                    }*/
                   
                   

                }
                /*foreach (Vertex v in needUpDate)
                {
                    v.publicPredicateImplications.Add(levelPotential);
                }*/
               // curentVertex.publicPredicateImplications.Add(levelPotential);
                curentVertex.canGetInParallel=levelPotential;
                //if (curentVertex.h + curentVertex.h2 == 0)
                if (curentVertex.h<=0)// + curentVertex.h2 == 0)
                {
                    curentVertex.publicPredicateImplications = new List<HashSet<CompoundFormula>>();
                    Vertex tmp = curentVertex;
                    while (tmp != null)
                    {
                        curentVertex.publicPredicateImplications.Insert(0, tmp.canGetInParallel);
                        tmp = tmp.Parent;
                    }
                    
                }
            }
            

            return null;
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
                    foreach(GroundedPredicate p in lEffects)
                        if(!p.Negation && a.PublicPredicates.Contains(p))
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


        public List<Vertex> Expand(Vertex v, HashSet<CompoundFormula> levelPotential, List<Vertex> needUpDate)
        {
            List<Vertex> lExpanded = new List<Vertex>();
            bool stop = false;
            int counter = -1;
            foreach (Agent agent in agents)
            {
                foreach (Action act in agent.publicActions)
                {
                    counter++;
                    if (counter <= v.actionNumber)
                    {
                        continue;
                    }
                    //if (act.Name.Contains("p1_black"))
                    //    Console.WriteLine("*");
                    Program.messages += agents.Count;
                    Vertex newVertex = v.Apply(act);
                    if (newVertex != null)
                    {
//                        if (act.Name.Contains("verysmooth"))
//                            Console.WriteLine("*");
                        lExpanded.Add(newVertex);
                        CompoundFormula effect = new CompoundFormula("and");
                        foreach (GroundedPredicate gp in act.HashEffects)
                        {
                            if (agent.PublicPredicates.Contains(gp))
                                effect.AddOperand(gp);
                        }
                        levelPotential.Add(effect);

                         if (newVertex.h < v.h && !first)
                        {
                            v.actionNumber = counter;
                            lExpanded.Add(v);
                            //stop = true;
                        }
                      //  needUpDate.Add(newVertex);
                    }
                    if (stop)
                        break;
                }
                if (stop)
                    break;
            }
            first = false;
            return lExpanded;

        }

        public Vertex FindMin(List<Vertex> lvertxs)
        {
            int index=0;
            int counter = 0;
            Vertex min = lvertxs.ElementAt(0);
            foreach (Vertex v in lvertxs)
            {
                if (Vertex.Comparer(min, v) == 1)
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
