using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class Order
    {
       public string type="";
       public Landmark lendmark1=null;
       public Landmark lendmark2=null;
       public Order(string typ ,Landmark l1, Landmark l2)
       {
           type = typ;
           lendmark1 = l1;
           lendmark2 = l2;
       }
       public override bool Equals(object obj)
       {
           if (obj is Order)
               return Equals((Order)obj);
           return false;
       }
       public  bool Equals(Order order2)
       {
           if (this.lendmark1.Equals(order2.lendmark1))
           {
               if (this.lendmark2.Equals(order2.lendmark2))
               {
                   return true;
               }
           }
           return false;
       }
        
    }
}
