using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    public class FunctionConstant : Constant
    {
        public GroundedFunctionPredicate Function { get; private set; }

        public FunctionConstant(GroundedFunctionPredicate f)
            : base("Function", f.Name)
        {
            Function = f;
        }

    }
}
