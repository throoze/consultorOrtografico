
import java.util.Iterator;
//@ model import org.jmlspecs.models.*;

/* Archivo ConsultOrt.java
 * Autor: Diego Mosquera
 * Creacion: 05/02/10
 * Modificacion: 15/02/10
 */

/**
 * Interfaz usada para modelar el TAD "Consultor Ortografico" para el proyecto 
 * de la materia "Algoritmos y Estructuras II" en la USB para el periodo Enero-
 * Marzo de 2010.
 * @author Diego Mosquera
 * @coauthor Victor De Ponte y Jose Zabala
 * @date 05/02/10
 * @updated 15/02/10
 * @updated 26/02/10
 */
public interface ConsultOrt {
    
    /*@ public model instance JMLValueSet vocabulario;
      @ public initially vocabulario != null && vocabulario.isEmpty();
      @*/

    /*@ public instance invariant true;
      @*/

    /*@ public normal_behavior
      @ requires bf(p)
      @          && 
      @          !vocabulario.has(new JMLString(p));
      @ ensures vocabulario.equals(
      @               \old(vocabulario).union(new JMLValueSet(new JMLString(p)))
      @         );
      @ assignable vocabulario;
      @
      @ also 
      @ public exceptional_behavior
      @ requires !bf(p)
      @          ||
      @          vocabulario.has(new JMLString(p));
      @ signals_only ExcepcionPalabraNoBienFormada,
      @              ExcepcionPalabraYaRegistrada;
      @ signals (ExcepcionPalabraNoBienFormada) !bf(p);
      @ signals (ExcepcionPalabraYaRegistrada)
      @ vocabulario.has(new JMLString(p));
      @ assignable \nothing;
      @*/			
    public void agregar(String p) throws
            ExcepcionPalabraNoBienFormada,	 
            ExcepcionPalabraYaRegistrada;

    /*@ public normal_behavior
      @ requires bf(pr);
      @ ensures vocabulario.equals(\old(vocabulario))
      @         &&
      @         (\forall int i, j ; 
      @                 0 <= i && i < \result.length
      @                 &&
      @                 0 <= j && j < \result.length
      @                 &&
      @                 i != j;
      @                         !\result[i].equals(\result[j])
      @         )
      @         &&
      @         (\forall int i ;
      @                 0 <= i && i < \result.length;
      @                         vocabulario.has(new JMLString(\result[i]))
      @         )
      @         &&
      @         (\forall int i ; 
      @                     0 <= i && i < \result.length
      @                                             ; ipf(pr, \result[i])
      @         );
      @ assignable \nothing;
      @
      @ also 
      @ public exceptional_behavior
      @ requires !bf(pr);
      @ signals_only ExcepcionPalabraNoBienFormada;
      @ signals (ExcepcionPalabraNoBienFormada) !bf(pr);
      @ assignable \nothing;
      @*/
    public String[] consultarPorPrefijo(String pr) throws 
	    ExcepcionPalabraNoBienFormada;

    /*Eliminado el siguiente pedazo de la postcondicion del normal_behavior:
      @         &&
      @         (\forall String s ; vocabulario.has(new JMLString(s))
      @             ; ipf(s, pl) ==> ipf(s, \result)
      @         );
     * razon: daba el mensaje siguiente:
     * warning: this quantifier is not executable...
     */
    /*@ public normal_behavior
      @ requires bf(pl);
      @ ensures vocabulario.equals(\old(vocabulario))
      @         &&
      @         ipf(\result, pl);
      @ assignable \nothing;
      @
      @ also 
      @ public exceptional_behavior
      @ requires !bf(pl);
      @ signals_only ExcepcionPalabraNoBienFormada;
      @ signals (ExcepcionPalabraNoBienFormada) !bf(pl);
      @ assignable \nothing;
      @*/
    public String prefijoMasLargo(String pl) throws 
	    ExcepcionPalabraNoBienFormada;

    //  p != "" --> !p.equals("")
    /*@ requires true;
      @ ensures \result <==> (!p.equals("")
      @             && 
      @             (\forall int i ; 0 <= i && i < p.length() 
      @                 ; 0 <= p.charAt(i) - 'a' 
      @                 &&
      @                 p.charAt(i) - 'a' <= 25 
      @             )
      @         );
      @*/
    public /*@ pure @*/ boolean  bf(String p);
	
    /*@ requires bf(p) && bf(q);
      @ ensures \result <==> p.length() <= q.length()
      @             &&
      @             (\forall int i ; 0 <= i && i < p.length() 
      @                 ; p.charAt(i) - q.charAt(i) == 0
      @             );
      @*/						   
    public /*@ pure @*/ boolean  ipf(String p, String q);
    
    /*@ requires true;
      @ ensures \result != null;
      @*/
    public Iterator elems ();
}