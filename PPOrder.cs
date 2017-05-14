using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class PPOrder
    {
       public string type="";
       public PrivacyPreservingLandmark lendmark1 = null;
       public PrivacyPreservingLandmark lendmark2 = null;
       public PPOrder(string typ, PrivacyPreservingLandmark l1, PrivacyPreservingLandmark l2)
       {
           type = typ;
           lendmark1 = l1;
           lendmark2 = l2;
       }
       public override string ToString()
       {
           string str = "";
           str=lendmark1.ToString()+" --> "+lendmark2.ToString();
           return str;
       }
        
    }
}
