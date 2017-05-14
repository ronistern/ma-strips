using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class HSPHeuristic 
    {
        private List<Action> actions;
        private List<Predicate> m_lGoal;
        public bool m_bMax;

        //the bMax flag is used to indicate using max or sum when computing a value for a set of Predicates
        public HSPHeuristic(List<Action>m_actions, List<Predicate> lGoal, bool bMax)
        {
            //m_dDomain = d;
            actions = m_actions;
            m_lGoal = lGoal;
            m_bMax = bMax;
        }

        public double h(State s)
        {
            if (Contains(s.m_lPredicates,m_lGoal))
                return 0;
            bool flag = true;
            bool notFind = true;
            double sum = 0;
            double max = 0;
            double depth=1;
            HashSet<Action> allReadyUse = new HashSet<Action>();
            Dictionary<GroundedPredicate, double> StatePredicates = new Dictionary<GroundedPredicate, double>();
           // State copyState = new State(s);
            foreach(GroundedPredicate prop in s.Predicates)
            {
                StatePredicates.Add(prop, 0);
            }
            while (flag)
            {
                flag = false;
                HashSet<GroundedPredicate> tempList = new HashSet<GroundedPredicate>();
                foreach (Action act in actions)
                {
                    if (allReadyUse.Contains(act))
                        continue;
                    if (Contains(StatePredicates, act.HashPrecondition))
                    {
                        allReadyUse.Add(act);
                        foreach (GroundedPredicate addProp in act.HashEffects)
                        {
                            if (!StatePredicates.ContainsKey(addProp) & !tempList.Contains(addProp))
                            {
                               // copyState.AddPredicate(addProp);
                                //StatePredicates.Add(addProp, depth);
                                tempList.Add(addProp);
                                flag = true;
                            }

                        }
                    }
                }
                foreach (GroundedPredicate prop in tempList)
                {
                    StatePredicates.Add(prop, depth);
                }

                depth++;

               // if (flag == false) return int.MaxValue;

                if (Contains(StatePredicates, m_lGoal))
                {
                    flag = false;
                    notFind = false;
                }


            }
            if(notFind)
                return int.MaxValue/2;

                foreach (GroundedPredicate tempProp in m_lGoal)
                {
                   sum+=StatePredicates[tempProp];
                    if(StatePredicates[tempProp]>max)
                        max=StatePredicates[tempProp];
                }


                if (m_bMax)
                    return max;
                else return sum;
            //your implementaiton here

        }
        
        private bool Contains(HashSet<Predicate> x, List<Predicate> y)
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
                if (!x.Contains(gP)) return false;
            }
            return true;
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
                if (!x.m_lPredicates.Contains(gP)) return false;
            }
            return true;
        }
        private bool Contains(Dictionary<GroundedPredicate,double> x, List<Predicate> y)
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
                if (!x.ContainsKey(gP)) return false;
            }
            return true;
        }

    }
}
