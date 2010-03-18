/**
 * Pequena clase que implementa los algoritmos de busqueda vistos en el curso: 
 * "Algoritmos y Estructuras II" de la Universidad Nacional Experimental Simon
 * Bolivar (busqueda lineal y binaria).
 * @version 1.1 23 de Enero de 2010
 * @author Victor De Ponte, 05-38087
 */
public class Buscar {

    /** 
     * Implementa la busqueda lineal en arreglos. Dice si el elemento esta y 
     * cual es su posicion.
     * @param a el arreglo de enteros a leer.
     * @param e el elemento a buscar en 'a'
     * @return pos posicion en la que se consiguio 'e'. esta=>(e>=0)
     */
    /*@ requires a.length>=0;
      @ 
      @ ensures (-1<=\result && \result<a.length) && 
      @         ((0<=\result && \result<a.length)==> a[\result]==e) &&
      @         ((\result==-1)==>(\forall int i ; 0<=i && i<a.length; a[i]!=e));
      @*/
    public static int lineal (int[] a, int e) {
        boolean esta=false;
        int pos=-1;
        /*@ loop_invariant 0<=k && k<=a.length &&
          @                (0<=pos&&pos<a.length)==>(a[pos]==e) &&
          @                (pos==-1)==>(\forall int i; 0<=i && i<k; a[i]!=e);
          @
          @ decreasing a.length-k;
          @
          @*/
        for (int k=0; k<a.length && !esta; k++) {
            if (a[k]==e) {
                esta=true;
                pos=k;
            }
        }
        return pos;
    }
    
    /** 
     * Implementa la busqueda lineal en arreglos para buscar el MENOR elemento
     * en el arreglo 'a' en el segmento '[i,f)'.
     * @param a el arreglo de enteros a leer.
     * @param i inicio del segmento en el que se va a buscar
     * @param f final del segmento en el que se va a buscar
     * @return pos - posicion en la que se consiguio el menor elemento.
     */
    /*@ requires 0<=a.length && 0<=i&&i<=f&&f<=a.length;
      @
      @ ensures (\forall int n; i<=n&&n<f; a[\result]<=a[n]);
      @*/
    public static int linealm (int[] a, int i, int f) {
        int pos=i;
        int aux=a[i];
		int k=i;
        /*@ loop_invariant 0<=k && k<=f &&
		  @                (\forall int n; i<=n&&n<k; a[pos]<=a[n]);
          @
          @ decreasing f-k;
          @*/
        for (k=i; k<f; k++) {
			if (a[k]<aux) {
				aux=a[k];
                pos=k;
            }
        }
        return pos;
    }

    /** 
     * Implementa la busqueda lineal en arreglos para buscar el MAYOR elemento
     * en el arreglo 'a' en el segmento '[i,f)'.
     * @param a el arreglo de enteros a leer.
     * @param i inicio del segmento en el que se va a buscar
     * @param f final del segmento en el que se va a buscar
     * @return pos - posicion en la que se consiguio el mayor elemento.
     */
    /*@ requires 0<=a.length && 0<=i&&i<=f&&f<=a.length;
      @
      @ ensures (\forall int n; i<=n&&n<f; a[\result]>=a[n]);
      @*/
    public static int linealM (int[] a, int i, int f) {
        int pos=i;
        int aux=a[i];
        /*@ loop_invariant i<=k && k<=f &&
		  @                (\forall int n; i<=n&&n<k; a[pos]>=a[n]);
          @
          @ decreasing f-k;
          @*/
        for (int k=i; k<f; k++) {
            if (a[k]>aux) {
                aux=a[k];
                pos=k;
            }
        }
        return pos;
    }

    /** 
     * Implementa la busqueda lineal en arreglos. Dice si el elemento esta y 
     * cual es su posicion.
     * @param a el arreglo de enteros a leer.
     * @param e el elemento a buscar en 'a'
     * @return esta booleano que indica si el elemento 'e' esta o no en 'a'
     */
    /*@ requires (a.length>=0);
      @ 
      @ ensures (\result<==>(\exists int i; 0<=i && i<a.length; a[i]==e));
      @*/
    public static boolean blineal (int[] a, int e) {
        boolean esta=false;
        /*@ loop_invariant 0<=k && k<=a.length &&
          @                (!esta)<==>(\forall int i; 0<=i && i<k; a[i]!=e);
          @
          @ decreasing a.length-k;
          @
          @*/
        for (int k=0; k<a.length && !esta; k++) {
            if (a[k]==e) {
                esta=true;
            }
        }
        return esta;
    }
    
    /**
     * Implementa la busqueda binaria en arreglos. Mas eficiente que la lineal.
     * Requiere que exista una relacion de orden para el tipo de elementos del 
     * arreglo y que el arreglo de entrada este ordenado.
     * @param a el arreglo de enteros a leer.
     * @param e el elemento a buscar en 'a'
     * @return pos posicion en la que se consiguio 'e'. esta=>(e>=0)
     */
    /*@ requires (a.length>=0) && 
      @          (\forall int i; 0<=i && i<a.length-1; a[i]<=a[i+1]);
      @ 
      @ ensures (-1<=\result && \result<a.length) && 
      @         ((0<=\result && \result<a.length)==> a[\result]==e) &&
      @         ((\result==-1)==>(\forall int i ; 0<=i && i<a.length; a[i]!=e));
      @*/
    public static int binaria (int[] a, int e) {
        int     pos=-1;
        int     izq=0;
        int     der=a.length;
        boolean esta=false;
        /*@ loop_invariant 0<=izq && izq<=der && der<=a.length &&
          @                (esta ||(\exists int i; izq<=i&&i<der; a[i]==e)<==>
          @                (\exists int i; 0<=i&&i<a.length; a[i]==e)) &&
          @                (esta ==> (0<=pos &&pos<a.length && a[pos]==e));
          @ 
          @ decreasing (der-izq)+(!esta ? 1:0);
          @*/
        while (izq!=der && !esta) {
            int med=(izq+der+1)/2;
            if (a[med]==e) {
                esta=true;
                pos=med;
            } else if (a[med]<e) {
                izq=med+1;
            } else if (a[med]>e) {
                der=med;
            }
        }
        return pos;
    }
    
    /**
     * Implementa la busqueda binaria en arreglos. Mas eficiente que la lineal.
     * Requiere que exista una relacion de orden para el tipo de elementos del 
     * arreglo y que el arreglo de entrada este ordenado.
     * @param a el arreglo de enteros a leer.
     * @param e el elemento a buscar en 'a'
     * @return esta booleano que indica si el elemento 'e' esta o no en 'a'
     */
    /*@ requires (a.length>=0) && 
      @          (\forall int i; 0<=i && i<a.length-1; a[i]<=a[i+1]);
      @ 
      @ ensures (\result<==>(\exists int i; 0<=i && i<a.length; a[i]==e));
      @*/
    public static boolean bbinaria (int[] a, int e) {
        int izq=0;
        int der=a.length;
        boolean esta=false;
        /*@ loop_invariant 0<=izq && izq<=der && der<=a.length &&
          @                (esta ||(\exists int i; izq<=i&&i<der; a[i]==e)<==>
          @                (\exists int i; 0<=i&&i<a.length; a[i]==e));
          @ 
          @ decreasing (der-izq)+(!esta ? 1:0);
          @*/
        while (izq!=der && !esta) {
            int med=(izq+der+1)/2;
            if (a[med]==e) {
                esta=true;
            } else if (a[med]<e) {
                izq=med+1;
            } else if (a[med]>e) {
                der=med;
            }
        }
        return esta;
    }
}