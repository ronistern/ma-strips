//using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Planning;

namespace Planning
{
    class ListOfStates
    {
        public HashSet<GroundedPredicate> states;
        public bool isGoal;
        public List<Action> notRelevantActions;
        public List<GroundedPredicate> addingKnowledge;
        
        public ListOfStates()
        {
            states = new HashSet<GroundedPredicate>();
            isGoal =false;
            notRelevantActions = new List<Action>();
            addingKnowledge = new List<GroundedPredicate>();
            
        }
    }
}
