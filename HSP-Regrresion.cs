using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class HSP_Regrresion : HeuristicFunction
    {
         private Domain m_dDomain;
        private List<Predicate> m_lGoal;
        private bool m_bMax;


        //the bMax flag is used to indicate using max or sum when computing a value for a set of Predicates
        public HSP_Regrresion(Domain d, List<Predicate> lGoal, bool bMax)
        {
            m_dDomain = d;
            m_lGoal = lGoal;
            m_bMax = bMax;
        }

        public override double h(State s)
        {
            return 0;
            //your implementaiton here

        }
    }
}
