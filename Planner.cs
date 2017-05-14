using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    abstract class Planner
    {
        protected Domain m_dDomain;
        public Planner(Domain d)
        {
            m_dDomain = d;
        }
        public abstract List<Action> Plan(Problem p);
        public abstract int ComputationCost();
    }
}
