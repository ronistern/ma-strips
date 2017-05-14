using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace Planning
{
    class PlanerHspAndLandmarks
    {
        List<Agent> agents = null;
        //Domain d;
        // Problem p;
        int countOfLandmarks = 0;
        List<Action> publicActions = null;
        public PlanerHspAndLandmarks(List<Agent> m_agents)
        {
            // d = m_d;
            // p = m_p;
            agents = m_agents;

            publicActions = new List<Action>();

            foreach (Agent agent in agents)
            {
                publicActions.AddRange(agent.publicActions);
                agent.initPlaner();


            }
            countOfLandmarks = agents[0].publicRelevantLandmark.Count;
            VertexHsp.initVertxClass(agents);
            //countOfLandmarks = (countOfLandmarks / agents.Count) * 2;


        }
       // public static int counter=0;
        public List<string> Plan()
        {

            bool bAllAgentsEqual = CheckAgentEquality();

            int i = 200;
            int[] statesNum = new int[agents.Count];
            for (int k = 0; k < statesNum.Length; k++)
            {
                statesNum[k] = 0;
            }


            VertexHsp rootVertexHsp = new VertexHsp(statesNum, new List<Action>(), 0, countOfLandmarks, 0, 0, null);
            rootVertexHsp.h = rootVertexHsp.ComputeFF_h(new bool[countOfLandmarks]);
            rootVertexHsp.ComputePreferActions();


            int count = 0;
            VertexHsp curentVertex = null;
            DateTime dtStart = DateTime.Now;

            DateTime begin = DateTime.Now;
            int queue1PriorityCounter = 0;
            int queue2PriorityCounter = 0;
            List<VertexHsp> queue = new List<VertexHsp>();
            List<VertexHsp> queue2 = new List<VertexHsp>();
            //   List<VertexHsp> queue2 = new List<VertexHsp>();
            bool first = true;
            bool first2 = true;
            HashSet<int[]> lVisited = new HashSet<int[]>(new ComparerArray());
            HashSet<VertexHsp> lVisited2 = new HashSet<VertexHsp>();

            queue.Add(rootVertexHsp);


            // lVisited.Add(rootVertexHsp.statesNubmber);
            // lVisited2.Add(rootVertexHsp);

            int temp = 0;
            List<string> lplan = null;
            bool flag = true;
            double minLandmark_h = countOfLandmarks;
            double minHsp_h = rootVertexHsp.h;
            int c = 0;
            int cResets = 0;
            double minh = 1000;
            int blindCounter = 0;
            TimeSpan tsDeadendDetection = new TimeSpan();
            try
            {
                while (queue.Count > 0 || queue2.Count > 0)
                {
                    c++;
                    if (c % 30 == 0 && curentVertex != null)
                    {

                        Console.Write("\rExpanded: " + c + ", open: " + queue.Count +
                            ", h: " + curentVertex.h + ", h2: " + curentVertex.h2 + ", T: " + (int)(DateTime.Now - dtStart).TotalSeconds
                            + ", deadend = " + (int)tsDeadendDetection.TotalSeconds);
                        if (queue.Count > 2000000)
                        {
                            return null;

                        }
                    }
                    flag = true;

                    temp++;
                    if (queue.Count > 0 && (queue1PriorityCounter > queue2PriorityCounter || queue2.Count == 0))
                    {
                        if (first)
                        {
                            first = false;
                            curentVertex = FindMinLandmarks(queue);
                        }
                        else
                        {
                            first = true;
                            curentVertex = FindMinHsp(queue);
                            queue1PriorityCounter--;
                        }
                        curentVertex = curentVertex.Calculate_h();
                    }
                    else
                    {
                        if (first2)
                        {
                            first2 = false;
                            curentVertex = FindMinLandmarks(queue2);
                        }
                        else
                        {
                            first2 = true;
                            curentVertex = FindMinHsp(queue2);
                            queue2PriorityCounter--;
                        }
                        curentVertex = curentVertex.Calculate_h();

                        if (curentVertex != null && (curentVertex.h2 < minLandmark_h || curentVertex.h < minHsp_h))
                        {
                            queue2PriorityCounter += 1000;
                        }
                    }
                    if (curentVertex == null)
                        continue;
                  //  counter++;
                  //  Console.WriteLine(counter);
                    
                    bool bVisited = false;
                    if (bAllAgentsEqual)
                        bVisited = lVisited2.Contains(curentVertex);
                    else
                        bVisited = lVisited.Contains(curentVertex.statesNubmber);


                    if (bVisited)
                        continue;
                    if (bAllAgentsEqual)
                        lVisited2.Add(curentVertex);
                    else
                        lVisited.Add(curentVertex.statesNubmber);



                    if (curentVertex.h2 < minLandmark_h)
                    {
                        minLandmark_h = curentVertex.h2;
                    }
                    if (curentVertex.h < minHsp_h)
                    {
                        minHsp_h = curentVertex.h;
                    }
                    // DateTime dtBefore = DateTime.Now;

                    //tsDeadendDetection += (DateTime.Now - dtBefore);

                    count++;

                    blindCounter++;

                    int f = 0;
                    List<VertexHsp> needUpDate = new List<VertexHsp>();
                    HashSet<CompoundFormula> levelPotential = new HashSet<CompoundFormula>();
                    int index = 1;
                    bool con = false;
                    Program.StateExpendCounter++;
                    List<VertexHsp> lExpanded = Expand(curentVertex, levelPotential, needUpDate);
                    /*if (lExpanded.Count == 0)
                    {
                            curentVertex.onlyPrefered = false;
                            lExpanded = Expand(curentVertex, levelPotential, needUpDate);
                    }*/

                    foreach (VertexHsp newVertexHsp in lExpanded)
                    {
                        f++;

                        newVertexHsp.g += (double)index / 1000000;

                        //bool bVisited = false;
                        /*  if(bAllAgentsEqual)
                              bVisited = lVisited2.Contains(newVertexHsp);
                          else
                              bVisited = lVisited.Contains(newVertexHsp.statesNubmber);
                          */

                        // if (!bVisited)
                        {
                            if (newVertexHsp.isPrefered)
                            {
                                queue2.Add(newVertexHsp);
                            }
                            else
                            {
                                queue.Add(newVertexHsp);
                            }
                            // queue2.Add(newVertexHsp);
                            // lVisited.Add(newVertexHsp.statesNubmber);
                            //lVisited2.Add(newVertexHsp);
                        }
                        index++;

                        /*if (minh > newVertexHsp.h)
                        {
                            minh = newVertexHsp.h;
                        
                        }*/

                        /*if (VertexHsp.Comparer(newVertexHsp, curentVertex) == -1 && !con)
                        {
                            blindCounter = 0;
                        }*/



                    }

                    curentVertex.canGetInParallel = levelPotential;

                    if (curentVertex.h == 0 || curentVertex.h2 == 0)
                    {
                        curentVertex.publicPredicateImplications = new List<HashSet<CompoundFormula>>();
                        VertexHsp tmp = curentVertex;
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

                            Program.times.Add(time);
                            Program.countActions.Add(lplan.Count);
                            Program.timeSum += time;
                            Program.actionSum += lplan.Count;



                            return lplan;
                        }
                        if (!isGoal.Equals("false"))
                        {

                        }
                    }
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex.ToString());
                return null;
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


        public List<VertexHsp> Expand(VertexHsp v, HashSet<CompoundFormula> levelPotential, List<VertexHsp> needUpDate)
        {
            List<VertexHsp> lExpanded = new List<VertexHsp>();
            foreach (Agent agent in agents)
            {
                foreach (Action act in agent.publicActions)
                {
                    //if (act.Name.Contains("p1_black"))
                    //    Console.WriteLine("*");
                    Program.messages += agents.Count;
                    VertexHsp newVertexHsp = v.OnlyApply(act);
                
                    if (newVertexHsp != null)
                    {
                       
                        lExpanded.Add(newVertexHsp);
                        CompoundFormula effect = new CompoundFormula("and");
                        foreach (GroundedPredicate gp in act.HashEffects)
                        {
                            if (agent.PublicPredicates.Contains(gp))
                                effect.AddOperand(gp);
                        }
                        levelPotential.Add(effect);
                        //  needUpDate.Add(newVertexHsp);
                    }
                }
            }
            return lExpanded;

        }

        public VertexHsp FindMinLandmarks(List<VertexHsp> lvertxs)
        {
            int index = 0;
            int counter = 0;
            VertexHsp min = lvertxs.ElementAt(0);
            foreach (VertexHsp v in lvertxs)
            {
                if (VertexHsp.LandmarksComparer(min, v) == 1)
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
        public VertexHsp FindMinHsp(List<VertexHsp> lvertxs)
        {
            int index = 0;
            int counter = 0;
            VertexHsp min = lvertxs.ElementAt(0);
            foreach (VertexHsp v in lvertxs)
            {
                if (VertexHsp.HspComparer(min, v) == 1)
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
