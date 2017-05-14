using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
        class ComparerList : IEqualityComparer<List<Predicate>>
        {
            public int code = -1;
            // Products are equal if their names and product numbers are equal. 
            public bool Equals(List<Predicate> x, List<Predicate> y)
            {

                return true;
            }

            // If Equals() returns true for a pair of objects  
            // then GetHashCode() must return the same value for these objects. 

            public int GetHashCode(List<Predicate> x)
            {
                if(code==-1)
                    code= ToString().GetHashCode();

                return code;
            }

        
        
    }
}
