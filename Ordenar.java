/**
 * Pequena clase que implementa los algoritmos de ordenamiento vistos en el 
 * curso: "Algoritmos y Estructuras II" de la Universidad Nacional Experimental 
 * Simon Bolivar (ordenamiento por: Insercion).
 * @version 1.0 15 de Enero de 2010
 * @author throoze
 */
public class Ordenar {
    
    /**
     * Funcion auxiliar que revisa si un arreglo de enteros esta ordenado.
     * @param a El arreglo a revisar.
     * @return 'true' si el arreglo 'a' esta ordenado de menor a mayor;
     * 'false' en caso contrario.
     */
    /*@ requires 0<=a.length;
      @
      @ ensures \result<==>(\forall int i; 0<=i&&i<a.length-1;a[i]<=a[i+1]);
      @*/
    public static boolean is (int[] a) {
       boolean is=true;
       /*@ loop_invariant 0<=k&&k<=a.length-1 &&
         @           is<==>(\forall int i; 0<=i&&i<k;a[i]<=a[i+1]);
         @
         @ decreasing (a.length-1)-k;
         @*/
       for (int k=0; k<a.length-1; k++) {
           if (a[k]>a[k+1]) {
               is=false;
           }
       }
       return is;
    }
    
    /**
     * Implementa el algoritmo de ordenamiento por Seleccion para arreglos de 
     * enteros.
     * @param arreglo el arreglo a ordenar
     */
    /*@ requires 0<=arreglo.length;
      @
      @ ensures (\forall int i; 0<=i&&i<arreglo.length-1;arreglo[i]<=
      @      arreglo[i+1]) && (\forall int i ; 0<=i && i<arreglo.length ; 
      @      (\exists int j ; 0<=j && j<arreglo.length ; \old(arreglo[i])==
      @      arreglo[j] && (\num_of int k ; 0<=k && k<arreglo.length ; 
      @      \old(arreglo[i])==\old(arreglo[k]))==(\num_of int k ; 0<=k &&
      @      k<arreglo.length ; arreglo[j]==arreglo[k])));
      @*/
    public static void seleccion (int[] arreglo) {
        /*@ loop_invariant 0<=k&&k<=arreglo.length &&
          @       (\forall int i; 0<=i&&i<k-1;arreglo[i]<=arreglo[i+1]) &&
          @       (\forall int i,j; 0<=i&&i<k && k<=j&&j<arreglo.length; 
          @       arreglo[i]<=arreglo[j]) && (\forall int i ; 0<=i && i<
          @       arreglo.length ; (\exists int j ; 0<=j && j<arreglo.length ; 
          @       \old(arreglo[i])==arreglo[j] && (\num_of int f ; 0<=f && 
          @       f<arreglo.length ; \old(arreglo[i])==\old(arreglo[f]))==
          @       (\num_of int f ; 0<=f && f<arreglo.length ; arreglo[j]==
          @       arreglo[f])));
          @
          @ decreasing arreglo.length-k;
          @
          @*/
        for (int k=0; k<arreglo.length; k++) {
            // Comienza la busqueda del menor en el segmento [k,arreglo.length)
            int pos=k;
            {
                int aux=arreglo[k];
                int c=k;
                /*@ loop_invariant k<=c && c<=arreglo.length &&
                  @        (\forall int n; k<=n&&n<c; arreglo[pos]<=arreglo[n]);
                  @
                  @ decreasing arreglo.length-c;
                  @*/
                for (c=k; c<arreglo.length; c++) {
                    if (arreglo[c]<aux) {
                        aux=arreglo[c];
                        pos=c;
                    }
                }
            }// Termina la busqueda del menor en el segmento [k,arreglo.length)
            
            {// Comienza intercambio arreglo[k] por arreglo[pos]
                int aux=arreglo[k];
                arreglo[k]=arreglo[pos];
                arreglo[pos]=aux;
            }// Termina intercambio arreglo[k] por arreglo[pos]
        }
    }
    
    /**
     * Implementa el algoritmo de Ordenamiento por Insercion para arreglos de 
     * enteros.
     * @param arreglo el arreglo a ordenar
     */
    /*@ requires 0<=arreglo.length;
      @
      @ ensures (\forall int i; 0<=i&&i<arreglo.length-1;arreglo[i]<=
      @       arreglo[i+1]) && (\forall int i ; 0<=i && i<arreglo.length ;
      @       (\exists int j ; 0<=j && j<arreglo.length ; \old(arreglo[i])==
      @       arreglo[j] && (\num_of int k ; 0<=k && k<arreglo.length ; 
      @       \old(arreglo[i])==\old(arreglo[k]))==(\num_of int k ; 0<=k &&
      @       k<arreglo.length ; arreglo[j]==arreglo[k])));
      @*/
    public static void insercion (int[] arreglo) {
        /*@ loop_invariant 0<=k&&k<=arreglo.length &&
          @       (\forall int i; 0<=i&&i<k-1;arreglo[i]<=arreglo[i+1]) &&
          @       (\forall int i ; 0<=i && i<arreglo.length ; (\exists int j ; 
          @       0<=j && j<arreglo.length ; \old(arreglo[i])==arreglo[j] && 
          @       (\num_of int n ; 0<=n && n<arreglo.length ; \old(arreglo[i])==
          @       \old(arreglo[n]))==(\num_of int n ; 0<=n && n<arreglo.length ;
          @       arreglo[j]==arreglo[n])));
          @
          @ decreasing arreglo.length-k;
          @
          @*/
        for (int k=0; k!=arreglo.length; k++) {
            int tmp=arreglo[k];
            int l=k;
            /*@ loop_invariant 0<=l&&l<=k &&
              @       (\forall int i;l+1<=i&&i<k+1; tmp<arreglo[i]) &&
              @       (\forall int i; 0<=i&&i<l-1;arreglo[i]<=arreglo[i+1]) &&
              @       (\forall int i; l+1<=i&&i<k;arreglo[i]<=arreglo[i+1]) &&
              @       (\forall int i,j; 0<=i&&i<l && l+1<=j&&j<k+1;arreglo[i]<=
              @       arreglo[j]) && (\forall int i; 0<=i&&i<arreglo.length; 
              @       (\exists int j; 0<=j && j<arreglo.length; \old(arreglo[i])
              @       ==arreglo[j] && ((\num_of int n; 0<=n && n<arreglo.length;
              @       \old(arreglo[i])==\old(arreglo[n]))-1)==(\num_of int f;
              @       0<=f&&f<arreglo.length ; arreglo[j]==arreglo[f]) && 
              @       (\forall int n; 0<=n && n<arreglo.length && 
              @       !(((\num_of int w; 0<=w&&w<arreglo.length; 
              @       \old(arreglo[i])==\old(arreglo[w]))-1)==(\num_of int w; 
              @       0<=w && w<arreglo.length ; arreglo[j]==arreglo[w]));
              @       n==tmp)));
              @
              @ decreasing l;
              @
              @*/
            for ( l=k; l!=0 && tmp<arreglo[l-1]; l--) {
                arreglo[l]=arreglo[l-1];
            }
            arreglo[l]=tmp;
        }
    }
    
    /**
     * Segundo procedimiento auxiliar para implementar el ordenamiento por mez-
     * cla. Se encarga de mezclar los arreglos ya ordenados.
     * @param a el arreglo ya ordenado.
     * @param izq el borde izquierdo del segmento a mezclar.
     * @param der el borde derecho del segmento a ordenar. 
     */
    /*@ requires 0 <= izq && izq <= der && der <= a.length &&
      @          (\forall int i,j; izq<=i&&i<((der+izq+1)/2)-1 && 
      @          ((der+izq+1)/2)<=j&&j<der-1; (a[i]<=a[i+1] && a[j]<=a[j+1]));
      @ 
      @ ensures (\forall int i; izq<=i&&i<der-1;a[i]<=a[i+1]) &&
      @         (\forall int i ; izq<=i && i<der ; (\exists int j ; izq<=j && 
      @         j<der ; \old(a[i])==a[j] && (\num_of int k ; izq<=k && 
      @         k<der ; \old(a[i])==\old(a[k]))==(\num_of int k ; izq<=k &&
      @         k<der ; a[j]==a[k]))) &&
      @    	    (\forall int i ; 0<=i && i<izq ; (\exists int j ; 0<=j && 
      @         j<izq ; \old(a[i])==a[j] && (\num_of int k ; 0<=k && 
      @         k<izq ; \old(a[i])==\old(a[k]))==(\num_of int k ; 0<=k &&
      @         k<izq ; a[j]==a[k]))) &&
      @         (\forall int i ; der<=i && i<a.length ; (\exists int j ; der<=j 
      @         && j<a.length ; \old(a[i])==a[j] && (\num_of int k ; der<=k && 
      @         k<a.length ; \old(a[i])==\old(a[k]))==(\num_of int k ; der<=k &&
      @         k<a.length ; a[j]==a[k])));
      @*/
    private static void mezclar (int[] a, int izq, int der) {
		System.out.println("Entro a mezclar con:");
		System.out.println("izq = "+izq);
		System.out.println("der = "+der);
        int m=(der+izq+1)/2;
        int[] aux= new int[der-izq];
        int l=izq;
        int r=m;
        int k=0;
/*
        /*@ loop_invariant 0<=k && k<=aux.length
          @                &&
          @                izq<=l && l<=m
          @                &&
          @                m<=r && r<=aux.length
          @                &&
          @                (l-izq)+(r-m) == k
          @                &&
          @                (\forall int i; izq<=i && i<k; aux[i]<=aux[i+1])
          @                &&
          @                (\forall int i; !(i<izq) && !(l<=i && i<m) && 
          @                !(der<=i) ; (\exists int j; 0<=j && j<k; a[i]==aux[j]
          @                && (\num_of int n;!(n<izq) && !(l<=n && n<m) && 
          @                !(der<=n); a[n]==a[i]) == (\num_of int n; 0<=n && n<k
          @                ;aux[n]==aux[j])))
          @                &&
          @                (\forall int i; izq<=i && i<der ; (\exists int j; 
          @                izq<=j && j<der; \old(a[i])==a[j] && (\num_of int n;
          @                izq<=n && n<der; \old(a[n])==\old(a[i])) == (\num_of 
          @                int n; izq<=n && n<der; a[n]==a[j])));
          @ 
          @ decreasing (der-izq)-k;
          @*/
        while (k<aux.length) {
            if (l<m && r<der && a[l]<=a[r]) {
                aux[k]=a[l];
                l++;
            } else if (l<m && r<der &&  a[r]<a[l]) {
                aux[k]=a[r];
                r++;
            } else if (m<=l && r<der) {
                aux[k]=a[r];
                r++;
            } else if (l<m && der<=r) {
                aux[k]=a[l];
                l++;
            }
            k++;
        }
        System.out.println("Este es el arreglo aux:   \n");
        System.out.print("{  ");
		for (k=0 ; k<aux.length ; k++) {
            System.out.print(aux[k]+"  ");
		}
        System.out.println("}");
        for (k=0; k<aux.length; k++) {
            a[izq+k]=aux[k];
        }
		System.out.println("Este es el arreglo a despues de llenarlo:   \n");
        System.out.print("{  ");
		for (k=0 ; k<a.length ; k++) {
            System.out.print(a[k]+"  ");
		}
        System.out.println("}\n");
    }
    
    /**
     * Primer procedimiento auxiliar para implementar el ordenamiento por mezcla
     * ("MergeSort"). Se encarga de hacer las llamadas recursivas y de llamar al
     * procedimiento que hace la mezcla.
     * @param a El arreglo sobre el que se va a trabajar.
     * @param izq Inicio del segmento que se va a ordenar.
     * @param der Final del segmento que se va a ordenar.
     */
    /*@ requires 0<=izq&&izq<=der&&der<=a.length;
      @
      @ ensures (\forall int i; izq<=i&&i<der-1;a[i]<=a[i+1]) &&
      @         (\forall int i ; izq<=i && i<der ; (\exists int j ; izq<=j && 
      @         j<der ; \old(a[i])==a[j] && (\num_of int k ; izq<=k && 
      @         k<der ; \old(a[i])==\old(a[k]))==(\num_of int k ; izq<=k &&
      @         k<der ; a[j]==a[k]))) &&
      @    	(\forall int i ; 0<=i && i<izq ; (\exists int j ; 0<=j && 
      @         j<izq ; \old(a[i])==a[j] && (\num_of int k ; 0<=k && 
      @         k<izq ; \old(a[i])==\old(a[k]))==(\num_of int k ; 0<=k &&
      @         k<izq ; a[j]==a[k]))) &
      @		(\forall int i ; der<=i && i<a.length ; (\exists int j ; der<=j 
      @		&& j<a.length ; \old(a[i])==a[j] && (\num_of int k ; der<=k && 
      @         k<a.length ; \old(a[i])==\old(a[k]))==(\num_of int k ; der<=k &&
      @         k<a.length ; a[j]==a[k])));
      @*/

	// decreasing der-izq;
    private static void ordMezcla (int[] a, int izq, int der) {
		System.out.println("Entro a ordMezcla con:");
		System.out.println("izq = "+izq);
		System.out.println("der = "+der);
        if (der-izq>1) {
            int med=(der+izq+1)/2;
			System.out.println("//@ assert izq<med&&med<der");
			System.out.println(izq+"<"+med+"<"+der);
			if (!(izq<med&&med<der))
				System.out.println("No se cumple la asercion...");
            //@ assert izq<med&&med<der;
            ordMezcla(a,izq,med);
            ordMezcla(a,med,der);
            mezclar(a, izq, der);
        }
    }
    
    /**
     * Procedimiento que implementa el ordenamiento por mezcla ("MergeSort").
     * @param a El arreglo a ordenar.
     */
    /*@ requires 0<=a.length;
      @
      @ ensures (\forall int i; 0<=i&&i<a.length-1;a[i]<=a[i+1]) &&
      @         (\forall int i ; 0<=i && i<a.length ; (\exists int j ; 0<=j && 
      @         j<a.length ; \old(a[i])==a[j] && (\num_of int k ; 0<=k && 
      @         k<a.length ; \old(a[i])==\old(a[k]))==(\num_of int k ; 0<=k &&
      @         k<a.length ; a[j]==a[k])));
      @*/
    public static void mergesort (int[] a) {
        ordMezcla(a, 0, a.length);
    }
    
}