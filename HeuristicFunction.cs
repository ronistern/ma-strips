using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    abstract class HeuristicFunction
    {
        public abstract double h(State s);
    }
}
