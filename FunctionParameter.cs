using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    public class FunctionParameter : Argument
    {
        public ParameterizedFunctionPredicate Function { get; private set; }

        public FunctionParameter(ParameterizedFunctionPredicate f) : base("Function", f.Name)
        {
            Function = f;
        }

     }
}
