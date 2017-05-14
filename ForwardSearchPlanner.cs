using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace Planning
{
    class ForwardSearchPlanner
    {
        private HSPHeuristic m_fHeuristic;
        private List<Action> actions;
        private int numOfState = 0;
        public ForwardSearchPlanner(List<Action> m_actions, HSPHeuristic fHeuristic)
            
        {
            m_fHeuristic = fHeuristic;
            actions = m_actions;
        }
        public  List<Action> Plan(State startState,List<Predicate> goal)
        {
            List<State> sortedOpenList = new List< State>();
            Dictionary<State, int> closeList = new Dictionary<State, int>();
            Dictionary<State, int> openList = new Dictionary<State, int>();
            sortedOpenList.Sort(compareFunction);

            startState.m_heuristic = (int)m_fHeuristic.h(startState);
            if (startState.m_heuristic == int.MaxValue/2)
                return null;
            sortedOpenList.Add(startState);
            if (Contains(startState, goal))
            {
                return new List<Action>();
            }
            openList.Add(startState,0);
           
           
            
            numOfState = 0;
            
            List<Action> Planning = new List<Action>();

            
            bool flag = false;
            State courentState = null;
            
            while (!flag)
            {
                if (sortedOpenList.Count == 0)
                    return null;


               
                courentState = sortedOpenList[0];
                sortedOpenList.RemoveAt(0);
                
                openList.Remove(courentState);
               
                
                closeList.Add(courentState, courentState.m_disFromStart);
                




                foreach (Action act in actions)
                {
                    
                    State next5tate =courentState.ApplyII(act);
                    if (next5tate != null)
                    {
                       
                        bool inCloseList = false;
                        
                        
                        if (closeList.ContainsKey(next5tate))
                        {
                            int oldDis = closeList[next5tate];
                            if (courentState.m_disFromStart + 1 >= oldDis)
                            {
                                continue;
                            }
                            else
                            {
                                closeList.Remove(next5tate);
                                inCloseList = true;
                            }
                               
                        }
                        if (!inCloseList)
                        {
                            if (openList.ContainsKey(next5tate))
                            {

                                int oldDis = openList[next5tate];
                                if (oldDis > courentState.m_disFromStart + 1)
                                {
                                    State st = null;
                                    foreach (State tempState in sortedOpenList)
                                    {
                                        if (tempState.Equals(next5tate))
                                        {


                                            st = tempState;

                                            break;
                                        }
                                    }
                                    if (st != null)
                                    {
                                        st.m_disFromStart = courentState.m_disFromStart + 1;
                                        st.prev = courentState;
                                        st.actToArrive = act;
                                        openList[next5tate] = courentState.m_disFromStart + 1;
                                        continue;
                                    }
                                    else
                                    {
                                        throw new Exception("buug");
                                    }

                                }
                                else
                                {
                                    continue;
                                }

                            }
                          

                        }
                       

                       
                            numOfState++;
                            next5tate.prev = courentState;
                            next5tate.actToArrive = act;
                            next5tate.m_disFromStart = courentState.m_disFromStart + 1;
                            next5tate.m_heuristic =(int)m_fHeuristic.h(next5tate);

                            if (Contains(next5tate, goal))
                            {
                                flag = true;
                                courentState = next5tate;
                                break;
                            }

                            sortedOpenList.Add(next5tate);
                            openList.Add(next5tate, next5tate.m_disFromStart);
                        
                       

                    }
                }
                if (m_fHeuristic.m_bMax)
                {
                    sortedOpenList.Sort(compareFunctionII);
                }
                else
                {
                    sortedOpenList.Sort(compareFunction);
                }
                

            }

            State tempState2 = courentState;

            
            while (tempState2.prev != null)
            {
                Planning.Insert(0, tempState2.actToArrive);
                tempState2 = tempState2.prev;

            }
            
            return Planning;

            //your implementaiton here
            
        }
        public int ComputationCost()
        {
            return numOfState;
        }
    
    public static int compareFunction(object d,object e)
    {
        int a = ((State)d).m_heuristic;// +((State)d).m_disFromStart;
        int b = ((State)e).m_heuristic;// +((State)e).m_disFromStart;
        
        if (a > b) 
            return 1;
        if (a < b) 
            return -1;
        if (a == b)
        {
            int g1 = ((State)d).m_disFromStart;
            int g2 = ((State)e).m_disFromStart;
            if (g1 > g2)
                return 1;
            if ((g1 < g2))
                return -1;
                    

        }
        return 0;

    }
    public static int compareFunctionII(object d, object e)
    {
        int a = ((State)d).m_heuristic+((State)d).m_disFromStart;
        int b = ((State)e).m_heuristic+((State)e).m_disFromStart;

        if (a > b) 
            return 1;
        if (a < b) 
            return -1;
        if (a == b)
        {
            int g1 = ((State)d).m_disFromStart;
            int g2 = ((State)e).m_disFromStart;
            if (g1 < g2)
                return -1;
            if ((g1 > g2))
                return 1;


        }
        return 0;

    }
    private bool Contains(State x, List<Predicate> y)
    {
        if (y == null)
            return true;
        if (x == null)
        {
            if (y.Count == 0)
                return true;
            return false;
        }
        foreach (GroundedPredicate gP in y)
        {
            if (!x.m_lPredicates.Contains(gP)) 
                return false;
        }
        return true;
    }
    }
}
