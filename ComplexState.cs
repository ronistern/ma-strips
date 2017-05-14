using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class ComplexState
    {
        public HashSet<GroundedPredicate>  state;
        public List<string> stringList;
        public List <Action> actionList;
        public List<Predicate> knowledge;
        public ComplexState(State s)
        {
            state = new HashSet<GroundedPredicate>();
            foreach (GroundedPredicate gp in s.m_lPredicates)
            {
                state.Add(gp);
            }
            
            stringList = new List<string>();
            stringList.Add("start");
            actionList = new List<Action>();
            knowledge = new List<Predicate>();
        }
        public ComplexState(HashSet<GroundedPredicate> s)
        {
            state = s;
            stringList = new List<string>();
            stringList.Add("start");
            actionList = new List<Action>();
            knowledge = new List<Predicate>();
        }

        public ComplexState(HashSet<GroundedPredicate> s, List<string> stringlist, List<Action> actionlist)
        {
            state = s;
            stringList = new List<string>();
            foreach (string str in stringlist)
            {
                stringList.Add(str);
            }
            actionList = new List<Action>();
            foreach (Action act in actionlist)
            {
                actionList.Add(act);
            }
           
        }

        public ComplexState(HashSet<GroundedPredicate> s, List<string> stringlist, List<Action> actionlist, List<GroundedPredicate> kl)
        {
            state = s;
            
            stringList = new List<string>();
            foreach (string str in stringlist)
            {
                stringList.Add(str);
            }
            
            actionList = new List<Action>();
            foreach (Action act in actionlist)
            {
                actionList.Add(act);
            }

            knowledge = new List<Predicate>();
            
            foreach (GroundedPredicate gp1 in kl)
            {
                
                knowledge.Add(gp1);
                
            }

            
        }
    }
}
