using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace Planning
{
    class PlanerHspII
    {
        List<Agent> agents = null;
        //Domain d;
       // Problem p;
        int countOfLandmarks = 0;
        List<Action> publicActions = null;
        public PlanerHspII(List<Agent> m_agents)
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
            VertexHspII.initVertxClass(agents);
            //countOfLandmarks = (countOfLandmarks / agents.Count) * 2;
           

        }

        public List<string> Plan()
        {

            bool bAllAgentsEqual = CheckAgentEquality();

            int i = 200;
            int[] statesNum = new int[agents.Count];
            for (int k = 0; k < statesNum.Length; k++)
            {
                statesNum[k] = 0;
            }


            VertexHspII rootVertexHspII = new VertexHspII(statesNum, new List<Action>(), 0, countOfLandmarks, 0, null);

           

            int count = 0;
            VertexHspII curentVertexHspII = null;
            DateTime dtStart = DateTime.Now;

            DateTime begin = DateTime.Now;
            List<VertexHspII> queue = new List<VertexHspII>();
            HashSet<int[]> lVisited = new HashSet<int[]>(new ComparerArray());
            HashSet<VertexHspII> lVisited2 = new HashSet<VertexHspII>();
           
            queue.Add(rootVertexHspII);
            lVisited.Add(rootVertexHspII.statesNubmber);
            lVisited2.Add(rootVertexHspII);
            
            int temp = 0;
            List<string> lplan = null;
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
                   
                    Console.Write("\rExpanded: " + c + ", open: " + queue.Count +
                        ", h: " + curentVertexHspII.h + ", h2: " + curentVertexHspII.h2 + ", T: " + (int)(DateTime.Now - dtStart).TotalSeconds 
                        + ", deadend = " + (int)tsDeadendDetection.TotalSeconds);
                    if (queue.Count > 200000)
                    {
                        return null;
                        
                    }
                }
                flag = true;
                
                temp++;
                curentVertexHspII = FindMin(queue);
                
                DateTime dtBefore = DateTime.Now;
               
                tsDeadendDetection += (DateTime.Now - dtBefore);
               
                count++;
               
                blindCounter++;
                
                int f = 0;
                List<VertexHspII> needUpDate = new List<VertexHspII>();
                HashSet<CompoundFormula> levelPotential = new HashSet<CompoundFormula>();
                int index = 1;
                bool con = false;
                List<VertexHspII> lExpanded = Expand(curentVertexHspII,  levelPotential,needUpDate);
                foreach (VertexHspII newVertexHspII in lExpanded)
                {
                    f++;

                    newVertexHspII.g += (double)index / 1000000;

                    bool bVisited = false;
                    if(bAllAgentsEqual)
                        bVisited = lVisited2.Contains(newVertexHspII);
                    else
                        bVisited = lVisited.Contains(newVertexHspII.statesNubmber);

                    if (!bVisited)
                    {
                        queue.Add(newVertexHspII);
                        lVisited.Add(newVertexHspII.statesNubmber);
                        lVisited2.Add(newVertexHspII);
                    }
                    index++;
                    if (minh > newVertexHspII.h)
                    {
                        minh = newVertexHspII.h;
                        
                    }

                    if (VertexHspII.Comparer(newVertexHspII, curentVertexHspII) == -1 && !con)
                    {
                        blindCounter = 0;
                    }
                   
                   

                }
                
                curentVertexHspII.canGetInParallel=levelPotential;
                
                //if (curentVertexHspII.h==0)
                {
                    curentVertexHspII.publicPredicateImplications = new List<HashSet<CompoundFormula>>();
                    VertexHspII tmp = curentVertexHspII;
                    while (tmp != null)
                    {
                        curentVertexHspII.publicPredicateImplications.Insert(0, tmp.canGetInParallel);
                        tmp = tmp.Parent;
                    }
                    string isGoal = curentVertexHspII.IsGoal(out lplan);
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


        public List<VertexHspII> Expand(VertexHspII v, HashSet<CompoundFormula> levelPotential, List<VertexHspII> needUpDate)
        {
            List<VertexHspII> lExpanded = new List<VertexHspII>();
            foreach (Agent agent in agents)
            {
                foreach (Action act in agent.publicActions)
                {
                    //if (act.Name.Contains("p1_black"))
                    //    Console.WriteLine("*");
                    Program.messages += agents.Count;
                    VertexHspII newVertexHspII = v.Apply(act);
                    if (newVertexHspII != null)
                    {
//                        if (act.Name.Contains("verysmooth"))
//                            Console.WriteLine("*");
                        lExpanded.Add(newVertexHspII);
                        CompoundFormula effect = new CompoundFormula("and");
                        foreach (GroundedPredicate gp in act.HashEffects)
                        {
                            if (agent.PublicPredicates.Contains(gp))
                                effect.AddOperand(gp);
                        }
                        levelPotential.Add(effect);
                      //  needUpDate.Add(newVertexHspII);
                    }
                }
            }
            return lExpanded;

        }

        public VertexHspII FindMin(List<VertexHspII> lvertxs)
        {
            int index=0;
            int counter = 0;
            VertexHspII min = lvertxs.ElementAt(0);
            foreach (VertexHspII v in lvertxs)
            {
                if (VertexHspII.Comparer(min, v) == 1)
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
        public VertexHspII FindMax(List<VertexHspII> lvertxs)
        {
            int index = 0;
            int counter = 0;
            VertexHspII max = lvertxs.ElementAt(0);
            foreach (VertexHspII v in lvertxs)
            {
                if (VertexHspII.Comparer(max, v) == -1)
                {
                    max = v;
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
