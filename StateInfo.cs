using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class StateInfo
    {
        public static int staticDifCounter=0;
        public State state = null;
        int code = -1;
        public  int difCounter = 0;
        public bool[] landmarksVector = null;
        public bool[] ReasonableOrdering = null;
        public bool[] actionVector = null;
        public bool[] satisfiedNew = null;
        public StateInfo prevStateInfo=null;
        public Dictionary<GroundedPredicate, int> publicPredicate = null;
        public StateInfo(State s, bool[] Landmarks, bool[] actions, bool[] m_ReasonableOrdering, bool[] m_satisfiedNew)
        {
            state = s;
            landmarksVector = Landmarks;
            actionVector = actions;
            ReasonableOrdering = m_ReasonableOrdering;
            satisfiedNew = m_satisfiedNew;
        }
        public StateInfo(StateInfo prev)
        {
            prevStateInfo = prev;
            difCounter = staticDifCounter;
            staticDifCounter++;
        }
        public StateInfo(State s, bool[] actions, Dictionary<GroundedPredicate, int> m_publicPredicate)
        {
            state = s;

            actionVector = actions;

            publicPredicate = m_publicPredicate;

        }
        public override bool Equals(object obj)
        {
            // return (GetHashCode() == ((State)obj).GetHashCode());
            if (obj is StateInfo)
            {
                if (difCounter != ((StateInfo)obj).difCounter)
                    return false;
                State s = ((StateInfo)obj).state;
                if (s.m_lPredicates.Count != state.m_lPredicates.Count)
                    return false;

                foreach (Predicate p in s.Predicates)
                    if (!state.Predicates.Contains(p))
                        return false;
                return true;

                //return m_lPredicates.Equals(s.m_lPredicates);
            }
            return false;
        }
        public override int GetHashCode()
        {
            if (code != -1) return code;
            code = difCounter;
            foreach (GroundedPredicate gp in state.m_lPredicates)
                code += gp.GetHashCode();
            return code;
        }

    }
}
