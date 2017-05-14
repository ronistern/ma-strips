using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace Planning
{
    class PlanerWeightedLandmarkAndHsp
    {
        List<Agent> agents = null;
        //Domain d;
       // Problem p;
        int countOfLandmarks = 0;
        List<Action> publicActions = null;
        public PlanerWeightedLandmarkAndHsp(List<Agent> m_agents)
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
            countOfLandmarks += agents[0].publicLandmarks.Count;
            VertexWeightedLandmarkAndHsp.initVertxClass(agents);
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


            VertexWeightedLandmarkAndHsp rootVertexHsp = new VertexWeightedLandmarkAndHsp(statesNum, new List<Action>(), 0,countOfLandmarks,0, 0, null);
            VertexWeightedLandmarkAndHsp.maxLandmarks = countOfLandmarks;
            VertexWeightedLandmarkAndHsp.maxHsp = rootVertexHsp.ComputeHsp();
            rootVertexHsp.h = VertexWeightedLandmarkAndHsp.maxHsp;

            int count = 0;
            VertexWeightedLandmarkAndHsp curentVertexHsp = null;
            DateTime dtStart = DateTime.Now;

            DateTime begin = DateTime.Now;
            List<VertexWeightedLandmarkAndHsp> queue = new List<VertexWeightedLandmarkAndHsp>();
            HashSet<int[]> lVisited = new HashSet<int[]>(new ComparerArray());
            HashSet<VertexWeightedLandmarkAndHsp> lVisited2 = new HashSet<VertexWeightedLandmarkAndHsp>();
           
            queue.Add(rootVertexHsp);
            lVisited.Add(rootVertexHsp.statesNubmber);
            lVisited2.Add(rootVertexHsp);
            
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
                        ", h: " + curentVertexHsp.h + ", h2: " + curentVertexHsp.h2 + ", T: " + (int)(DateTime.Now - dtStart).TotalSeconds 
                        + ", deadend = " + (int)tsDeadendDetection.TotalSeconds);
                    if (queue.Count > 200000)
                    {
                        return null;
                        
                    }
                }
                flag = true;
                
                temp++;
                curentVertexHsp = FindMin(queue);
                
                DateTime dtBefore = DateTime.Now;
               
                tsDeadendDetection += (DateTime.Now - dtBefore);
               
                count++;
               
                blindCounter++;
                
                int f = 0;
                List<VertexWeightedLandmarkAndHsp> needUpDate = new List<VertexWeightedLandmarkAndHsp>();
                HashSet<CompoundFormula> levelPotential = new HashSet<CompoundFormula>();
                int index = 1;
                bool con = false;
                List<VertexWeightedLandmarkAndHsp> lExpanded = Expand(curentVertexHsp,  levelPotential,needUpDate);
                foreach (VertexWeightedLandmarkAndHsp newVertexHsp in lExpanded)
                {
                    f++;

                    newVertexHsp.g += (double)index / 1000000;

                    bool bVisited = false;
                    if(bAllAgentsEqual)
                        bVisited = lVisited2.Contains(newVertexHsp);
                    else
                        bVisited = lVisited.Contains(newVertexHsp.statesNubmber);

                    if (!bVisited)
                    {
                        queue.Add(newVertexHsp);
                        lVisited.Add(newVertexHsp.statesNubmber);
                        lVisited2.Add(newVertexHsp);
                    }
                    index++;
                    if (minh > newVertexHsp.h)
                    {
                        minh = newVertexHsp.h;
                        
                    }

                    /*if (VertexWeightedLandmarkAndHsp.Comparer(newVertexHsp, curentVertexHsp) == -1 && !con)
                    {
                        blindCounter = 0;
                    }*/
                   
                   

                }
                
                curentVertexHsp.canGetInParallel=levelPotential;
                
                if (curentVertexHsp.h==0)
                {
                    curentVertexHsp.publicPredicateImplications = new List<HashSet<CompoundFormula>>();
                    VertexWeightedLandmarkAndHsp tmp = curentVertexHsp;
                    while (tmp != null)
                    {
                        curentVertexHsp.publicPredicateImplications.Insert(0, tmp.canGetInParallel);
                        tmp = tmp.Parent;
                    }
                    string isGoal = curentVertexHsp.IsGoal(out lplan);
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


        public List<VertexWeightedLandmarkAndHsp> Expand(VertexWeightedLandmarkAndHsp v, HashSet<CompoundFormula> levelPotential, List<VertexWeightedLandmarkAndHsp> needUpDate)
        {
            List<VertexWeightedLandmarkAndHsp> lExpanded = new List<VertexWeightedLandmarkAndHsp>();
            foreach (Agent agent in agents)
            {
                foreach (Action act in agent.publicActions)
                {
                    //if (act.Name.Contains("p1_black"))
                    //    Console.WriteLine("*");
                    Program.messages += agents.Count;
                    VertexWeightedLandmarkAndHsp newVertexHsp = v.Apply(act);
                    if (newVertexHsp != null)
                    {
//                        if (act.Name.Contains("verysmooth"))
//                            Console.WriteLine("*");
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

        public VertexWeightedLandmarkAndHsp FindMin(List<VertexWeightedLandmarkAndHsp> lvertxs)
        {
            int index=0;
            int counter = 0;
            VertexWeightedLandmarkAndHsp min = lvertxs.ElementAt(0);
            foreach (VertexWeightedLandmarkAndHsp v in lvertxs)
            {
                if (VertexWeightedLandmarkAndHsp.HspComparer(min, v) == 1)
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
